(* Pass "defun" -- `let f = function | (g_, tm, vhs) -> ..` becomes
   `let f (g_, tm, vhs) = match tm with ..`.

   SML's `fun f = fn (G, U, Vs) => ...` came over as a `function` over the whole
   tuple, so a reader cannot tell which argument is actually being analysed. Every
   tuple position whose pattern is irrefutable in *every* branch is hoisted into a
   parameter; the scrutinee narrows to the positions that vary. Arity and type are
   unchanged -- both forms take one tuple -- so no call site moves.

   Two stages, split on what proves the rewrite correct rather than on how many
   positions move:

   - Default (DEFUN / DEFUN1): a hoisted position binds the *same* `Ppat_var` in
     every branch, or `_` in every branch. Capture-free by construction -- every
     body that could mention the name already had it bound to that component, and
     `| g_, Foo g_, vhs` is not legal OCaml, so no branch can be seeing an outer
     binding. Core.verify is then a complete check: shape is all there is.

   - `--with-any` (DEFUNANY): some branches bind `_` where others bind the name.
     Those `_` branches saw whatever `g_` the enclosing scope held, and hoisting
     captures them:

       let g_ = outer in
       let f = function
         | g_, A, vhs -> use g_        (* the component *)
         | _,  B, vhs -> use g_        (* the OUTER g_ -- captured *)

     Scoping is invisible to an AST comparison and the types often coincide, so
     this stage rests on a token scan, not on the verifier. Sites needing it are
     DEFERANY under the default stage -- deferred whole, never half-hoisted, so
     the second run still sees a `function` to rewrite.

   Subcommands: refactor defun [locate|patch] [scope] [--with-any] *)

open Parsetree
open Asttypes
open Core

(* What a position's pattern looks like across all branches. *)
type pos = Uni of string option (* all `Ppat_var n`, or all `_` *) | Mix of string | Vary

type slot = Var of string | Any

type plan = {
  slots : slot array;   (* the parameter tuple, one entry per position *)
  vary : int list;      (* positions left in the scrutinee, ascending *)
  single : bool;        (* degenerate one-branch form: no `match` at all *)
}

type site = {
  key : int;            (* `function` keyword offset -- anchors the text edits *)
  ck : int;             (* Pfunction_cases offset -- keys the intent mapper *)
  insert_at : int;      (* end of the last existing parameter, else end of the name *)
  arrow_end : int;      (* single form only: just past the sole `->` *)
  plan : plan;
  cases : case list;
  ln : int;
}

(* ------------------------------------------------------------------ *)
(* Locating                                                            *)
(* ------------------------------------------------------------------ *)

(* Pfunction_cases' own location runs from the first case, not from the keyword,
   and `let f x = function ..` is one Pexp_function whose loc starts at `x`. So
   the keyword is found from the cases backwards, over whitespace and the
   optional leading bar. *)
let find_function_kw src at =
  if at + 8 <= String.length src && String.sub src at 8 = "function" then Some at
  else
    let j = skip_ws_back src (at - 1) in
    let j = if j >= 0 && src.[j] = '|' then skip_ws_back src (j - 1) else j in
    if j >= 7 && String.sub src (j - 7) 8 = "function" then Some (j - 7) else None

let no_comment src s e =
  let rec go i = i + 1 >= e || (not (src.[i] = '(' && src.[i + 1] = '*') && go (i + 1)) in
  s >= 0 && e <= String.length src && go s

(* A case pattern is rewritten by concatenating the *kept* components' source
   text, so comments inside those survive; anything commented in a dropped
   component or between components would be deleted. `| g_, Omitapx (.., r
   (* = Vhs *)), vhs ->` is the common shape and must not be declined for a
   comment sitting in the component that stays. *)
let comments_only_in ~keep src s e =
  let rec go i =
    if i + 1 >= e then true
    else if List.exists (fun (ks, ke) -> i >= ks && i < ke) keep then go (i + 1)
    else if src.[i] = '(' && src.[i + 1] = '*' then false
    else go (i + 1)
  in
  s >= 0 && e <= String.length src && go s

(* Identifier tokens occurring in [s,e). *)
let range_words src s e =
  let tbl = Hashtbl.create 64 in
  let buf = Buffer.create 32 in
  let flush () =
    if Buffer.length buf > 0 then (Hashtbl.replace tbl (Buffer.contents buf) (); Buffer.clear buf)
  in
  for i = s to min (e - 1) (String.length src - 1) do
    let c = src.[i] in
    if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_' || c = '\''
    then Buffer.add_char buf c
    else flush ()
  done;
  flush ();
  tbl

let comps_of p =
  match p.ppat_desc with
  | Ppat_tuple (cs, Closed) when List.for_all (fun (l, _) -> l = None) cs -> Some (List.map snd cs)
  | _ -> None

let classify_pat p =
  match p.ppat_desc with
  | Ppat_var { txt; _ } when p.ppat_attributes = [] -> `V txt
  | Ppat_any when p.ppat_attributes = [] -> `A
  | _ -> `O

(* Fold one position's per-branch classifications into a verdict. *)
let pos_of col =
  let names = List.filter_map (function `V n -> Some n | _ -> None) col in
  let anys = List.exists (( = ) `A) col in
  let others = List.exists (( = ) `O) col in
  let distinct = List.sort_uniq compare names in
  if others then Vary
  else
    match (distinct, anys) with
    | [], true -> Uni None
    | [ n ], false -> Uni (Some n)
    | [ n ], true -> Mix n
    | _ -> Vary

(* A parameter for a varying position is bound over the whole `match`, so the
   region that can be captured is exactly the cases -- not the whole file. Judging
   candidates there instead of against `file_words` is both sound and far less
   blunt: nearly every file in the tree contains some `a`, which would otherwise
   push every name out to `a2`, `a4`, ... for no gain.

   A case whose own pattern binds `n` at that very position is exempt: it re-binds
   `n` to the component the parameter already holds, so the shadowing is inert. *)
let case_words src c =
  range_words src c.pc_lhs.ppat_loc.loc_start.pos_cnum c.pc_rhs.pexp_loc.loc_end.pos_cnum

let usable src cases i n =
  List.for_all
    (fun c ->
      match comps_of c.pc_lhs with
      | Some cs when i >= 0 && classify_pat (List.nth cs i) = `V n -> true
      | _ -> not (Hashtbl.mem (case_words src c) n))
    cases

(* Prefer a name a branch already gives the position; the most common one wins a
   tie. Failure degrades to a fresh name and never declines a site. *)
let derive_name src cases i =
  let names =
    List.filter_map
      (fun c ->
        match comps_of c.pc_lhs with
        | Some cs -> ( match classify_pat (List.nth cs i) with `V n -> Some n | _ -> None)
        | None -> None)
      cases
  in
  let ranked =
    List.sort_uniq compare names
    |> List.map (fun n -> (-List.length (List.filter (( = ) n) names), n))
    |> List.sort compare |> List.map snd
  in
  List.find_opt (usable src cases i) ranked

let fresh src cases taboo =
  let base = [| "a"; "b"; "c"; "d"; "e"; "g"; "h" |] in
  let name i = if i < Array.length base then base.(i) else "v" ^ string_of_int i in
  let rec go i =
    let n = name i in
    if (not (List.mem n !taboo)) && usable src cases (-1) n then (taboo := n :: !taboo; n)
    else go (i + 1)
  in
  go 0

let sites_of ~with_any src ast =
  let acc = ref [] in
  let decline ln why = acc := Error (ln, why) :: !acc in
  let visit vb =
    match vb.pvb_expr.pexp_desc with
    | Pexp_function (params, None, Pfunction_cases (cases, cl, []))
      when vb.pvb_expr.pexp_attributes = [] && vb.pvb_constraint = None && cases <> [] ->
        let ln = cl.loc_start.pos_lnum in
        let cols = List.map (fun c -> comps_of c.pc_lhs) cases in
        if List.exists (( = ) None) cols then
          (* Reconciliation: every tupled `= function` an independent scan finds
             must land in exactly one bucket here, so the skips are counted too. *)
          decline ln "skip: a case pattern is not an unlabelled closed tuple"
        else
          let cols = List.map Option.get cols in
          let arity = List.length (List.hd cols) in
          if arity < 2 || List.exists (fun c -> List.length c <> arity) cols then
            decline ln "skip: arity < 2, or branches disagree on arity"
          else
            let verdicts =
              List.init arity (fun i -> pos_of (List.map (fun c -> classify_pat (List.nth c i)) cols))
            in
            let uni_n = List.length (List.filter (function Uni _ -> true | _ -> false) verdicts) in
            let mix_n = List.length (List.filter (function Mix _ -> true | _ -> false) verdicts) in
            if uni_n = 0 && mix_n = 0 then
              decline ln "skip: no position is irrefutable in every branch"
            else if mix_n > 0 && not with_any then
              decline ln "mixed `_`/name position -- deferred to the --with-any stage"
            else
              let hoisted = function Uni _ -> true | Mix _ -> with_any | Vary -> false in
              let vary =
                List.init arity (fun i -> i)
                |> List.filter (fun i -> not (hoisted (List.nth verdicts i)))
              in
              let single = vary = [] in
              if single && (List.length cases > 1 || (List.hd cases).pc_guard <> None) then
                decline ln "every position irrefutable but more than one branch (or a guard)"
              else
                (match find_function_kw src cl.loc_start.pos_cnum with
                | None -> decline ln "no `function` keyword before the cases"
                | Some fstart ->
                    let insert_at =
                      match List.rev params with
                      | p :: _ -> p.pparam_loc.loc_end.pos_cnum
                      | [] -> vb.pvb_pat.ppat_loc.loc_end.pos_cnum
                    in
                    let between = insert_at >= 0 && insert_at <= fstart
                                  && String.trim (String.sub src insert_at (fstart - insert_at)) = "=" in
                    let pats_clean =
                      List.for_all
                        (fun c ->
                          let l = c.pc_lhs.ppat_loc in
                          let cs = Option.get (comps_of c.pc_lhs) in
                          let keep =
                            List.map
                              (fun i ->
                                let p = List.nth cs i in
                                expand_parens src p.ppat_loc.loc_start.pos_cnum
                                  p.ppat_loc.loc_end.pos_cnum)
                              vary
                          in
                          (not l.loc_ghost)
                          && comments_only_in ~keep src l.loc_start.pos_cnum l.loc_end.pos_cnum)
                        cases
                    in
                    (* Names for the scrutinee positions, then the parameter tuple.
                       Hoisted names are taboo so a fresh one cannot collide. *)
                    let taboo =
                      ref
                        (List.filter_map
                           (fun v -> match v with Uni (Some n) | Mix n -> Some n | _ -> None)
                           verdicts)
                    in
                    let vnames =
                      List.map
                        (fun i ->
                          match derive_name src cases i with
                          | Some n when not (List.mem n !taboo) ->
                              taboo := n :: !taboo;
                              bump "name: reused a branch binder";
                              (i, n)
                          | _ -> bump "name: fresh"; (i, fresh src cases taboo))
                        vary
                    in
                    let slots =
                      Array.init arity (fun i ->
                          match List.nth verdicts i with
                          | Uni (Some n) -> Var n
                          | Uni None -> Any
                          | Mix n -> Var n
                          | Vary -> Var (List.assoc i vnames))
                    in
                    let arrow_end =
                      if not single then -1
                      else
                        let j = skip_ws_fwd src (List.hd cases).pc_lhs.ppat_loc.loc_end.pos_cnum in
                        if j + 2 <= String.length src && String.sub src j 2 = "->" then j + 2 else -1
                    in
                    if not between then decline ln "text between the binder and `function` is not a bare `=`"
                    else if not pats_clean then decline ln "comment inside a case pattern"
                    else if single && arrow_end < 0 then decline ln "no `->` after the sole case"
                    else if single && not (no_comment src fstart arrow_end) then
                      decline ln "comment between `function` and `->`"
                    else
                      acc :=
                        Ok { key = fstart; ck = cl.loc_start.pos_cnum; insert_at; arrow_end;
                             plan = { slots; vary; single }; cases; ln }
                        :: !acc)
    | Pexp_function (_, _, Pfunction_cases (_, cl, _)) ->
        decline cl.loc_start.pos_lnum "skip: constrained binding, attributes, or no cases"
    | _ -> ()
  in
  let it =
    { Ast_iterator.default_iterator with
      value_binding = (fun self vb -> visit vb; Ast_iterator.default_iterator.value_binding self vb);
      attribute = (fun _ _ -> ())
    }
  in
  (match ast with Impl st -> it.structure it st | Intf sg -> it.signature it sg);
  List.rev !acc

(* ------------------------------------------------------------------ *)
(* Text                                                                *)
(* ------------------------------------------------------------------ *)

let slot_text = function Var n -> n | Any -> "_"
let params_text pl = "(" ^ String.concat ", " (Array.to_list pl.slots |> List.map slot_text) ^ ")"
let scrut_text pl = String.concat ", " (List.map (fun i -> slot_text pl.slots.(i)) pl.vary)

(* A component's own parentheses may sit outside its location; taking the bare
   range would turn `| g_, (A | B), vhs ->` into `| A | B ->`. *)
let comp_text src p =
  let s, e = expand_parens src p.ppat_loc.loc_start.pos_cnum p.ppat_loc.loc_end.pos_cnum in
  String.sub src s (e - s)

let case_repl src pl c =
  let cs = Option.get (comps_of c.pc_lhs) in
  String.concat ", " (List.map (fun i -> comp_text src (List.nth cs i)) pl.vary)

let edits_of file src st =
  let pl = st.plan in
  let ed s e repl kind = { file; s; e; repl; kind; line = st.ln; note = params_text pl } in
  if pl.single then
    (* Collapse `= function | p ->` to `(p) =` in one edit; a separate insert
       would leave the keyword line blank. *)
    [ ed st.insert_at st.arrow_end (" " ^ params_text pl ^ " =") "DEFUN1" ]
  else
    ed st.insert_at st.insert_at (" " ^ params_text pl) "DEFUN"
    :: ed st.key (st.key + 8) ("match " ^ scrut_text pl ^ " with") "DEFUN"
    :: List.map
         (fun c ->
           let l = c.pc_lhs.ppat_loc in
           ed l.loc_start.pos_cnum l.loc_end.pos_cnum (case_repl src pl c) "DEFUN")
         st.cases

(* ------------------------------------------------------------------ *)
(* Intent                                                              *)
(* ------------------------------------------------------------------ *)

let mknoloc txt = { Location.txt; loc = Location.none }

let map_param self p =
  match p.pparam_desc with
  | Pparam_val (l, d, pat) ->
      { p with pparam_desc =
                 Pparam_val (l, Option.map (self.Ast_mapper.expr self) d, self.Ast_mapper.pat self pat) }
  | Pparam_newtype _ -> p

let intent (plans : (int, plan) Hashtbl.t) =
  let open Ast_mapper in
  { default_mapper with
    expr =
      (fun self ex ->
        match ex.pexp_desc with
        | Pexp_function (params, None, Pfunction_cases (cases, cl, []))
          when Hashtbl.mem plans (cl.loc_start.pos_cnum) ->
            let pl = Hashtbl.find plans cl.loc_start.pos_cnum in
            let params = List.map (map_param self) params in
            let cases =
              List.map
                (fun c ->
                  { pc_lhs = self.pat self c.pc_lhs;
                    pc_guard = Option.map (self.expr self) c.pc_guard;
                    pc_rhs = self.expr self c.pc_rhs })
                cases
            in
            let tuple =
              Ast_helper.Pat.tuple
                (Array.to_list pl.slots
                |> List.map (function
                     | Var n -> (None, Ast_helper.Pat.var (mknoloc n))
                     | Any -> (None, Ast_helper.Pat.any ())))
                Closed
            in
            let param = { pparam_loc = Location.none;
                          pparam_desc = Pparam_val (Nolabel, None, tuple) } in
            let body =
              if pl.single then
                (List.hd cases).pc_rhs
              else
                let narrow c =
                  let cs = Option.get (comps_of c.pc_lhs) in
                  match pl.vary with
                  | [ i ] -> List.nth cs i
                  | vs -> Ast_helper.Pat.tuple (List.map (fun i -> (None, List.nth cs i)) vs) Closed
                in
                let scrut =
                  match pl.vary with
                  | [ i ] -> Ast_helper.Exp.ident (mknoloc (Longident.Lident (slot_text pl.slots.(i))))
                  | vs ->
                      Ast_helper.Exp.tuple
                        (List.map
                           (fun i ->
                             (None, Ast_helper.Exp.ident (mknoloc (Longident.Lident (slot_text pl.slots.(i))))))
                           vs)
                in
                Ast_helper.Exp.match_ scrut
                  (List.map (fun c -> { c with pc_lhs = narrow c }) cases)
            in
            { ex with pexp_desc = Pexp_function (params @ [ param ], None, Pfunction_body body) }
        | _ -> default_mapper.expr self ex)
  }

(* ------------------------------------------------------------------ *)
(* Per-file classification                                             *)
(* ------------------------------------------------------------------ *)

let classify ~with_any file src ast =
  let raw = sites_of ~with_any src ast in
  let declines =
    List.filter_map
      (function
        | Error (ln, why) ->
            let skip = String.length why >= 5 && String.sub why 0 5 = "skip:" in
            bump (if skip then why else "decline: " ^ why);
            Some { file; s = 0; e = 0; repl = ""; kind = (if skip then "SKIP" else "DECLINE");
                   line = ln; note = why }
        | Ok _ -> None)
      raw
  in
  let sts = List.filter_map (function Ok st -> Some st | Error _ -> None) raw in
  (* The text edits anchor on the keyword offset, the intent mapper on the
     Pfunction_cases offset; a site carries both so the two never drift. *)
  let check group eds =
    let h = Hashtbl.create 8 in
    List.iter (fun st -> Hashtbl.replace h st.ck st.plan) group;
    verify ~path:file ~src ~original:ast ~intent:(intent h) eds
  in
  declines
  @
  if sts = [] then []
  else
    let all = List.concat_map (edits_of file src) sts in
    match check sts all with
    | None -> all
    | Some _ ->
        (* Isolate: a single bad site must not cost the file. *)
        List.concat_map
          (fun st ->
            let eds = edits_of file src st in
            match check [ st ] eds with
            | None -> eds
            | Some why ->
                (match Sys.getenv_opt "REFACTOR_DUMP" with
                 | Some dir ->
                     write_file
                       (Filename.concat dir (Filename.basename file ^ "." ^ string_of_int st.ln ^ ".dump"))
                       (splice src eds)
                 | None -> ());
                bump ("decline: " ^ why);
                [ { file; s = 0; e = 0; repl = ""; kind = "ESCALATE"; line = st.ln; note = why } ])
          sts

let applied_kinds = [ "DEFUN"; "DEFUN1" ]

let main args =
  let with_any = List.mem "--with-any" args in
  let args = List.filter (fun a -> not (String.length a > 1 && a.[0] = '-')) args in
  let cmd = match args with c :: _ -> c | [] -> "locate" in
  let scope = match args with _ :: s :: _ -> Some s | _ -> None in
  let files =
    all_files scan_roots
    |> List.filter (fun f ->
           match scope with
           | None -> true
           | Some p -> String.length f >= String.length p && String.sub f 0 (String.length p) = p)
  in
  let scan () =
    edits := [];
    Hashtbl.reset diag;
    List.iter
      (fun f ->
        match parse_file f with
        | exception e -> Printf.eprintf "PARSE FAIL %s: %s\n" f (Printexc.to_string e)
        | src, ast -> List.iter add (classify ~with_any f src ast))
      files;
    let all = !edits in
    let auto = List.filter (fun e -> List.mem e.kind applied_kinds) all in
    let kept, deferred = non_overlapping auto in
    (all, auto, kept, deferred)
  in
  let report all auto kept deferred =
    let count k = List.length (List.filter (fun e -> e.kind = k) all) in
    Printf.eprintf "DEFUN=%d DEFUN1=%d ESCALATE=%d DECLINE=%d SKIP=%d | auto=%d kept=%d overlap-deferred=%d\n"
      (count "DEFUN") (count "DEFUN1") (count "ESCALATE") (count "DECLINE") (count "SKIP")
      (List.length auto) (List.length kept) (List.length deferred);
    Hashtbl.fold (fun k v acc -> (k, v) :: acc) diag []
    |> List.sort compare
    |> List.iter (fun (k, v) -> Printf.eprintf "  %-62s %5d\n" k v)
  in
  if cmd = "locate" then begin
    let all, auto, kept, deferred = scan () in
    report all auto kept deferred;
    List.iter
      (fun e -> Printf.printf "%s\t%s:%d\t%s\t%s\n" e.kind e.file e.line e.note (escape e.repl))
      (List.sort (fun a b -> compare (a.file, a.line) (b.file, b.line)) all)
  end
  else if cmd = "patch" then begin
    let all, auto, kept, deferred = scan () in
    report all auto kept deferred;
    if kept <> [] then begin
      let ne, nf = apply kept in
      Printf.eprintf "patched %d edits across %d files\n" ne nf
    end
  end
  else (Printf.eprintf "usage: refactor defun [locate|patch] [scope] [--with-any]\n"; exit 1)
