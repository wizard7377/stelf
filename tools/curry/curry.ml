(* curry -- mechanical SML-tuple-style -> curried-style refactoring tool.

   Operates purely on the Parsetree (no type information), so it is immune to
   comments, string literals and paren-matching edge cases that defeat a
   regex-based rewriter. Every rewrite it declines to make is backstopped by the
   type checker once signatures change, so conservatism is always safe.

   Subcommands:
     curry targets   list the tupled `val` declarations it will act on
     curry locate    classify every site (AUTO / ESCALATE) and write a report
     curry patch     apply the AUTO edits in place

   See docs/curry-sites.txt for the report and the plan for the safety argument. *)

open Parsetree
open Asttypes

module ISet = Set.Make (Int)

(* Width 2-3 is the mechanical pass; >=4 is hand-designed (records / labelled
   args) and deliberately excluded -- see plan Phase E. *)
let min_arity = 2
let max_arity = 3

let scan_roots = [ "src"; "test"; "bin" ]
let excluded_dirs = [ "_build"; ".git"; "basis"; "twelf"; "tools"; "examples"; "exercises" ]

(* ------------------------------------------------------------------ *)
(* File helpers                                                        *)
(* ------------------------------------------------------------------ *)

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let write_file path s =
  let oc = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () -> output_string oc s)

let rec walk acc dir =
  match Sys.readdir dir with
  | exception Sys_error _ -> acc
  | entries ->
      Array.fold_left
        (fun acc e ->
          let p = Filename.concat dir e in
          if Sys.is_directory p then
            if List.mem e excluded_dirs then acc else walk acc p
          else if Filename.check_suffix p ".ml" || Filename.check_suffix p ".mli" then p :: acc
          else acc)
        acc entries

let all_files roots = List.concat_map (fun r -> walk [] r) roots |> List.sort compare

type parsed = Impl of structure | Intf of signature

let parse_file path =
  let src = read_file path in
  let lb = Lexing.from_string src in
  Location.init lb path;
  let ast =
    if Filename.check_suffix path ".mli" then Intf (Parse.interface lb)
    else Impl (Parse.implementation lb)
  in
  (src, ast)

(* ------------------------------------------------------------------ *)
(* Source-text utilities                                               *)
(* ------------------------------------------------------------------ *)

let sub src (l : Location.t) = String.sub src l.loc_start.pos_cnum (l.loc_end.pos_cnum - l.loc_start.pos_cnum)
let is_ws c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

let rec skip_ws_back src i = if i >= 0 && is_ws src.[i] then skip_ws_back src (i - 1) else i
let rec skip_ws_fwd src i = if i < String.length src && is_ws src.[i] then skip_ws_fwd src (i + 1) else i

(* Index of the ')' matching the '(' at [i], or None. Naive w.r.t. comments and
   strings, which is safe here: it is only ever called on a range the parser
   already told us is a single expression. *)
let match_paren src i =
  let n = String.length src in
  let rec go i d =
    if i >= n then None
    else
      match src.[i] with
      | '(' -> go (i + 1) (d + 1)
      | ')' -> if d = 1 then Some i else go (i + 1) (d - 1)
      | _ -> go (i + 1) d
  in
  if i < n && src.[i] = '(' then go i 0 else None

(* If [s,e) is wrapped in a redundant matched paren pair, widen to include it.
   Handles the case where a node's location excludes its own parentheses. *)
let expand_parens src s e =
  let b = skip_ws_back src (s - 1) in
  if b >= 0 && src.[b] = '(' then
    match match_paren src b with
    | Some close when skip_ws_fwd src e = close -> (b, close + 1)
    | _ -> (s, e)
  else (s, e)

(* Does the text stand alone as a function argument without added parens? *)
let is_atom t =
  let t = String.trim t in
  let n = String.length t in
  if n = 0 then false
  else
    let ident =
      (t.[0] = '_' || (t.[0] >= 'a' && t.[0] <= 'z') || (t.[0] >= 'A' && t.[0] <= 'Z'))
      && String.for_all
           (fun c ->
             (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
             || c = '_' || c = '\'' || c = '.')
           t
    in
    if ident then true
    else if String.for_all (fun c -> c >= '0' && c <= '9') t then true
    else if t.[0] = '(' then match_paren t 0 = Some (n - 1)
    else if t.[0] = '[' then t.[n - 1] = ']'
    else false

let wrap t = if is_atom t then String.trim t else "(" ^ t ^ ")"

(* ------------------------------------------------------------------ *)
(* Targets: tupled `val` declarations                                  *)
(* ------------------------------------------------------------------ *)

let targets : (string, ISet.t) Hashtbl.t = Hashtbl.create 512

(* Which file declared each target, so a batch can be scoped to the names owned
   by one library while still patching their call sites wherever those live. *)
let origins : (string, string list) Hashtbl.t = Hashtbl.create 512

let add_target ?(origin = "") name arity =
  let cur = try Hashtbl.find targets name with Not_found -> ISet.empty in
  Hashtbl.replace targets name (ISet.add arity cur);
  if origin <> "" then
    let os = try Hashtbl.find origins name with Not_found -> [] in
    if not (List.mem origin os) then Hashtbl.replace origins name (origin :: os)

(* Unlabelled tuple only: a labelled tuple component is a different construct. *)
let tuple_parts_ty (ct : core_type) =
  match ct.ptyp_desc with
  | Ptyp_tuple parts when List.for_all (fun (l, _) -> l = None) parts ->
      Some (List.map snd parts)
  | _ -> None

let val_tuple_arg (vd : value_description) =
  match vd.pval_type.ptyp_desc with
  | Ptyp_arrow (Nolabel, arg, _) -> tuple_parts_ty arg
  | _ -> None

let collect_targets files =
  let cur = ref "" in
  let it =
    { Ast_iterator.default_iterator with
      value_description =
        (fun self vd ->
          (match val_tuple_arg vd with
          | Some parts ->
              let n = List.length parts in
              if n >= min_arity && n <= max_arity then
                add_target ~origin:!cur vd.pval_name.txt n
          | None -> ());
          Ast_iterator.default_iterator.value_description self vd)
    }
  in
  List.iter
    (fun f ->
      (* Only src/ declares the project's signatures; test/ never does. *)
      if String.length f >= 4 && String.sub f 0 4 = "src/" then begin
        cur := f;
        match parse_file f with
        | exception _ -> ()
        | _, Impl st -> it.structure it st
        | _, Intf sg -> it.signature it sg
      end)
    files

(* Scope the batch: keep only targets declared under [prefix]. Call sites are
   still rewritten wherever they occur -- coupling, not directory, is the unit. *)
let restrict_to prefix =
  let drop =
    Hashtbl.fold
      (fun name _ acc ->
        let os = try Hashtbl.find origins name with Not_found -> [] in
        let owned =
          List.exists
            (fun o -> String.length o >= String.length prefix && String.sub o 0 (String.length prefix) = prefix)
            os
        in
        if owned then acc else name :: acc)
      targets []
  in
  List.iter (Hashtbl.remove targets) drop

(* basis/ is a submodule that deliberately mirrors the tuple-style SML Basis
   Library API and stays tupled permanently. Several of its functions share a
   name with a project target (Int.compare, List.drop, String.extract), so a
   name-keyed rewrite would claim them. Decline anything qualified by a Basis
   module. Read from the submodule rather than hardcoded, to stay in sync. *)
let basis_modules =
  let dir = "basis/lib" in
  match Sys.readdir dir with
  | exception Sys_error _ -> Hashtbl.create 1
  | entries ->
      let t = Hashtbl.create 128 in
      Array.iter
        (fun e -> if Filename.check_suffix e ".ml" then Hashtbl.replace t (Filename.remove_extension e) ())
        entries;
      t

let is_basis_qualified (lid : Longident.t) =
  match Longident.flatten lid with q :: _ :: _ -> Hashtbl.mem basis_modules q | _ -> false

(* A name is actionable only if its arity is unambiguous. The 9 names carrying
   two different arities are skipped; the compiler will flag them. *)
let target_arity name =
  match Hashtbl.find_opt targets name with
  | Some s when ISet.cardinal s = 1 -> Some (ISet.choose s)
  | _ -> None

(* ------------------------------------------------------------------ *)
(* Triviality: guards the evaluation-order hazard                      *)
(* ------------------------------------------------------------------ *)

(* Currying `f (g (), h ())` into `f (g ()) (h ())` swaps one unspecified
   evaluation order for another. Auto-patch only when at most one component can
   have an effect. *)
let rec is_trivial (e : expression) =
  match e.pexp_desc with
  | Pexp_ident _ | Pexp_constant _ -> true
  | Pexp_construct (_, None) | Pexp_variant (_, None) -> true
  | Pexp_construct (_, Some a) | Pexp_variant (_, Some a) -> is_trivial a
  | Pexp_tuple parts -> List.for_all (fun (_, p) -> is_trivial p) parts
  | Pexp_array parts -> List.for_all is_trivial parts
  | Pexp_field (a, _) -> is_trivial a
  | Pexp_constraint (a, _) -> is_trivial a
  | _ -> false

(* ------------------------------------------------------------------ *)
(* Edits                                                               *)
(* ------------------------------------------------------------------ *)

type edit = {
  file : string;
  s : int;
  e : int;
  repl : string;
  kind : string;  (* SIG | DEF | DEFFUN | CALL | ESCALATE *)
  line : int;
  note : string;
}

let edits : edit list ref = ref []
let add ed = edits := ed :: !edits

(* Reconciliation counters: every application of a target name that the tool
   declines is tallied by reason, so the delta against the independent scan can
   be explained category by category rather than by a percentage. *)
let diag : (string, int) Hashtbl.t = Hashtbl.create 16
let bump k = Hashtbl.replace diag k (1 + try Hashtbl.find diag k with Not_found -> 0)

(* Identifiers already present in a file -- used to pick non-shadowing parameter
   names when rewriting a `function`-bodied definition.

   Whole-file scope is what makes this sound, including against names a file
   inherits from an `open`. To be broken by shadowing, a case body would have to
   *reference* the shadowed name, which means writing it -- so it would appear as
   a token here and the candidate would be rejected. Shadowing a binding that the
   body never mentions is inert. *)
let file_words src =
  let tbl = Hashtbl.create 1024 in
  let n = String.length src in
  let buf = Buffer.create 32 in
  let flush () =
    if Buffer.length buf > 0 then (Hashtbl.replace tbl (Buffer.contents buf) (); Buffer.clear buf)
  in
  for i = 0 to n - 1 do
    let c = src.[i] in
    if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_' || c = '\''
    then Buffer.add_char buf c
    else flush ()
  done;
  flush ();
  tbl

let fresh_names words arity =
  let base = [| "a"; "b"; "c"; "d" |] in
  let rec try_suffix k =
    let cand = List.init arity (fun i -> base.(i) ^ if k = 0 then "" else string_of_int k) in
    if List.exists (fun c -> Hashtbl.mem words c) cand then try_suffix (k + 1) else cand
  in
  try_suffix 0

(* ------------------------------------------------------------------ *)
(* Per-file analysis                                                   *)
(* ------------------------------------------------------------------ *)

let analyse file src ast =
  let words = file_words src in
  let line (l : Location.t) = l.loc_start.pos_lnum in
  let ok (l : Location.t) = (not l.loc_ghost) && l.loc_end.pos_cnum > l.loc_start.pos_cnum in

  (* --- signatures: `a * b -> c` becomes `a -> b -> c` --- *)
  let do_val (vd : value_description) =
    match val_tuple_arg vd with
    | Some parts when target_arity vd.pval_name.txt = Some (List.length parts) ->
        let arg =
          match vd.pval_type.ptyp_desc with Ptyp_arrow (_, a, _) -> a | _ -> assert false
        in
        if ok arg.ptyp_loc && List.for_all (fun p -> ok p.ptyp_loc) parts then begin
          let s, e = expand_parens src arg.ptyp_loc.loc_start.pos_cnum arg.ptyp_loc.loc_end.pos_cnum in
          let repl = String.concat " -> " (List.map (fun p -> sub src p.ptyp_loc) parts) in
          add { file; s; e; repl; kind = "SIG"; line = line arg.ptyp_loc; note = vd.pval_name.txt }
        end
    | _ -> ()
  in

  (* --- call sites --- *)
  (* Callee positions, so a target name used as a *value* can be told apart from
     one being applied. Value uses (`Timers.time Timers.printing expToString x`)
     cannot be rewritten mechanically and become build residue -- report them. *)
  let callee_pos = Hashtbl.create 256 in
  let do_apply (e : expression) =
    (match e.pexp_desc with
    | Pexp_apply (fn, _) -> Hashtbl.replace callee_pos fn.pexp_loc.loc_start.pos_cnum ()
    | _ -> ());
    match e.pexp_desc with
    | Pexp_apply ({ pexp_desc = Pexp_ident lid; pexp_loc = floc; _ }, (Nolabel, arg) :: _) -> (
        let name = Longident.last lid.txt in
        (* A decline is not "nothing to do" -- it is work the build will surface
           as a type error later. Emit it as a located row so the residue can be
           enumerated up front and worked as a list, rather than met one
           compilation unit at a time (`@check` reports only the first error per
           unit, so an n-site file costs n build iterations to discover). *)
        let decline reason =
          bump ("decline: " ^ reason);
          add { file; s = e.pexp_loc.loc_start.pos_cnum; e = e.pexp_loc.loc_end.pos_cnum;
                repl = ""; kind = "DECLINE"; line = line e.pexp_loc;
                note = String.concat "." (Longident.flatten lid.txt) ^ " -- " ^ reason }
        in
        (if Hashtbl.mem targets name && is_basis_qualified lid.txt then
           bump "decline: basis-qualified callee (out of scope)"
         else if Hashtbl.mem targets name then
           match (target_arity name, arg.pexp_desc) with
           | None, _ -> decline "name has ambiguous arity"
           | Some ar, Pexp_tuple parts when List.length parts <> ar -> decline "tuple arity mismatch"
           | Some _, Pexp_tuple parts when not (List.for_all (fun (l, _) -> l = None) parts) ->
               decline "labelled tuple"
           | Some _, Pexp_tuple _ -> ()
           | Some _, _ -> decline "argument is not a literal tuple");
        match (target_arity name, arg.pexp_desc) with
        | Some ar, Pexp_tuple parts
          when (not (is_basis_qualified lid.txt))
               && List.length parts = ar
               && List.for_all (fun (l, _) -> l = None) parts ->
            let parts = List.map snd parts in
            if ok floc && List.for_all (fun p -> ok p.pexp_loc) parts then begin
              (* Anchor on the '(' after the callee and paren-match it. This is
                 correct whether or not the tuple's own location includes the
                 parens, and it makes `f ((a, b))` -> `f a b` fall out. *)
              let lp = skip_ws_fwd src floc.loc_end.pos_cnum in
              match match_paren src lp with
              | None -> ()
              | Some rp ->
                  (* Sanity: the tuple the parser found must live inside the
                     paren pair we just matched. *)
                  let tup_s = arg.pexp_loc.loc_start.pos_cnum in
                  if tup_s >= lp && arg.pexp_loc.loc_end.pos_cnum <= rp + 1 then begin
                    let ntriv = List.length (List.filter (fun p -> not (is_trivial p)) parts) in
                    let repl =
                      String.concat " " (List.map (fun p -> wrap (sub src p.pexp_loc)) parts)
                    in
                    if ntriv > 1 then
                      add { file; s = lp; e = rp + 1; repl; kind = "ESCALATE";
                            line = line e.pexp_loc; note = name ^ " (>1 effectful arg)" }
                    else
                      add { file; s = lp; e = rp + 1; repl; kind = "CALL";
                            line = line e.pexp_loc;
                            note = String.concat "." (Longident.flatten lid.txt) }
                  end
            end
        | _ -> ())
    | Pexp_ident lid
      when Hashtbl.mem targets (Longident.last lid.txt)
           && (not (is_basis_qualified lid.txt))
           && (not (Hashtbl.mem callee_pos e.pexp_loc.loc_start.pos_cnum))
           && target_arity (Longident.last lid.txt) <> None ->
        bump "valueuse: target name passed as a value (residue)";
        add { file; s = e.pexp_loc.loc_start.pos_cnum; e = e.pexp_loc.loc_end.pos_cnum;
              repl = ""; kind = "VALUEUSE"; line = line e.pexp_loc;
              note = String.concat "." (Longident.flatten lid.txt) }
    | _ -> ()
  in

  (* --- definitions --- *)
  let rec pat_ok ar (p : pattern) =
    match p.ppat_desc with
    | Ppat_tuple (parts, Closed) -> List.length parts = ar
    | Ppat_any | Ppat_var _ -> true
    | Ppat_or (a, b) -> pat_ok ar a && pat_ok ar b
    | Ppat_alias (a, _) | Ppat_constraint (a, _) -> pat_ok ar a
    | _ -> false
  in
  let do_binding (vb : value_binding) =
    match vb.pvb_pat.ppat_desc with
    | Ppat_var nm -> (
        match target_arity nm.txt with
        | None -> ()
        | Some ar -> (
            match vb.pvb_expr.pexp_desc with
            (* let f (x, y) = body *)
            | Pexp_function
                ({ pparam_desc = Pparam_val (Nolabel, None, ({ ppat_desc = Ppat_tuple (parts, Closed); _ } as p));
                   pparam_loc; _ }
                :: _, _, _)
              when List.length parts = ar && List.for_all (fun (l, _) -> l = None) parts ->
                let parts = List.map snd parts in
                if ok pparam_loc && List.for_all (fun q -> ok q.ppat_loc) parts then begin
                  ignore p;
                  let s, e = expand_parens src pparam_loc.loc_start.pos_cnum pparam_loc.loc_end.pos_cnum in
                  let repl = String.concat " " (List.map (fun q -> wrap (sub src q.ppat_loc)) parts) in
                  add { file; s; e; repl; kind = "DEF"; line = line pparam_loc; note = nm.txt }
                end
            (* let f = function | (p1, p2) -> ... *)
            | Pexp_function ([], None, Pfunction_cases (cases, cloc, _))
              when cases <> [] && List.for_all (fun c -> pat_ok ar c.pc_lhs) cases
                   && List.exists
                        (fun c -> match c.pc_lhs.ppat_desc with Ppat_tuple _ -> true | _ -> false)
                        cases ->
                let fstart = cloc.loc_start.pos_cnum in
                let after_name = vb.pvb_pat.ppat_loc.loc_end.pos_cnum in
                let between = String.sub src after_name (fstart - after_name) in
                (* Guard: only a bare `=` may sit between the name and `function`,
                   so a type annotation is never silently deleted. *)
                if String.trim between = "=" && fstart + 8 <= String.length src
                   && String.sub src fstart 8 = "function"
                then begin
                  let names = fresh_names words ar in
                  let repl =
                    " " ^ String.concat " " names ^ " = match " ^ String.concat ", " names ^ " with"
                  in
                  add { file; s = after_name; e = fstart + 8; repl; kind = "DEFFUN";
                        line = line cloc; note = nm.txt }
                end
            | _ -> ()))
    | _ -> ()
  in

  let it =
    { Ast_iterator.default_iterator with
      value_description = (fun self vd -> do_val vd; Ast_iterator.default_iterator.value_description self vd);
      expr = (fun self e -> do_apply e; Ast_iterator.default_iterator.expr self e);
      value_binding = (fun self vb -> do_binding vb; Ast_iterator.default_iterator.value_binding self vb);
      (* Do not descend into attribute payloads. `[@@deriving eq, ord, show]`
         parses as a structure of bare identifiers, so `eq` and `show` -- which
         are also target names -- were being reported as value uses. They are
         deriver names, not references. Skipping also guarantees the patcher can
         never splice bytes inside a payload, where a rewrite would be silently
         wrong. *)
      attribute = (fun _ _ -> ())
    }
  in
  match ast with Impl st -> it.structure it st | Intf sg -> it.signature it sg

(* ------------------------------------------------------------------ *)
(* Driver                                                              *)
(* ------------------------------------------------------------------ *)

let escape s =
  String.concat "\\n" (String.split_on_char '\n' s) |> fun s ->
  if String.length s > 90 then String.sub s 0 90 ^ "..." else s

(* Nested call sites produce overlapping ranges (`f (g (a,b), c)`). Keep the
   outer edit and drop the inner one.

   Return the dropped *edits*, not a count. A fresh `curry patch` invocation does
   NOT pick them up: `collect_targets` reads the tree as it finds it, so once run
   1 has rewritten `val g : a * b -> c` to `val g : a -> b -> c`, `g` is no
   longer a target and the deferred inner `g (a, b)` is never looked at again --
   it survives as a type error with no row in curry-sites.txt pointing at it.
   `patch` therefore loops in-process (see patch_rounds), where `targets` stays
   populated across rounds. *)
let non_overlapping eds =
  (* Group by file first -- offsets from different files are incomparable. *)
  let sorted =
    List.sort
      (fun a b ->
        match compare a.file b.file with
        | 0 -> ( match compare a.s b.s with 0 -> compare b.e a.e | c -> c)
        | c -> c)
      eds
  in
  let kept, dropped, _, _ =
    List.fold_left
      (fun (kept, dropped, cur_file, last_end) ed ->
        if ed.file <> cur_file then (ed :: kept, dropped, ed.file, ed.e)
        else if ed.s >= last_end then (ed :: kept, dropped, cur_file, ed.e)
        else (kept, ed :: dropped, cur_file, last_end))
      ([], [], "", min_int) sorted
  in
  (List.rev kept, List.rev dropped)

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let with_escalate = List.mem "--with-escalate" args in
  let args = List.filter (fun a -> not (String.length a > 1 && a.[0] = '-')) args in
  let cmd = match args with c :: _ -> c | [] -> "locate" in
  let scope = match args with _ :: s :: _ -> Some s | _ -> None in
  let files = all_files scan_roots in
  collect_targets files;
  (match scope with
  | Some p ->
      restrict_to p;
      Printf.eprintf "scoped to targets declared under %s: %d names\n" p (Hashtbl.length targets)
  | None -> ());
  if cmd = "targets" then begin
    let names = Hashtbl.fold (fun k v acc -> (k, v) :: acc) targets [] |> List.sort compare in
    List.iter
      (fun (n, s) -> Printf.printf "%-28s %s\n" n (String.concat "," (List.map string_of_int (ISet.elements s))))
      names;
    Printf.printf "\n%d target names (arity %d-%d)\n" (List.length names) min_arity max_arity
  end
  else begin
    (* One analysis pass over the tree as it currently sits on disk. `patch`
       calls this repeatedly, so it must start from a clean slate each time. *)
    let scan () =
      edits := [];
      Hashtbl.reset diag;
      List.iter
        (fun f ->
          match parse_file f with
          | exception e -> Printf.eprintf "PARSE FAIL %s: %s\n" f (Printexc.to_string e)
          | src, ast -> analyse f src ast)
        files;
      let all = !edits in
      (* VALUEUSE and DECLINE are report-only: never applied by `patch`.
         Whitelisting the applied kinds -- rather than blacklisting -- is what
         makes adding a report-only kind safe.

         ESCALATE joins them under --with-escalate. Leaving it out is not the
         safe default it looks like: every escalated site's name also receives a
         SIG edit (126 of 126, checked), so skipping the call sites while
         currying their signature yields 126 guaranteed type errors rather than
         126 preserved call sites. The kind is kept separate so `locate` still
         reports them and the review record survives. *)
      let kinds =
        [ "SIG"; "DEF"; "DEFFUN"; "CALL" ] @ if with_escalate then [ "ESCALATE" ] else []
      in
      let auto = List.filter (fun e -> List.mem e.kind kinds) all in
      let kept, deferred = non_overlapping auto in
      (all, auto, kept, deferred)
    in
    let report all auto kept deferred =
      let count k = List.length (List.filter (fun e -> e.kind = k) all) in
      Printf.eprintf
        "SIG=%d DEF=%d DEFFUN=%d CALL=%d ESCALATE=%d VALUEUSE=%d DECLINE=%d | auto=%d kept=%d overlap-deferred=%d\n"
        (count "SIG") (count "DEF") (count "DEFFUN") (count "CALL") (count "ESCALATE")
        (count "VALUEUSE") (count "DECLINE")
        (List.length auto) (List.length kept) (List.length deferred);
      Hashtbl.fold (fun k v acc -> (k, v) :: acc) diag []
      |> List.sort compare
      |> List.iter (fun (k, v) -> Printf.eprintf "  %-46s %5d\n" k v)
    in
    (* Apply a round's edits. Bottom-up within each file so earlier ranges stay
       valid. Returns (edits applied, files written). *)
    let apply kept =
      let by_file = Hashtbl.create 64 in
      List.iter
        (fun e ->
          let cur = try Hashtbl.find by_file e.file with Not_found -> [] in
          Hashtbl.replace by_file e.file (e :: cur))
        kept;
      let nf = ref 0 and ne = ref 0 in
      Hashtbl.iter
        (fun f eds ->
          let src = read_file f in
          (* Descending by offset so earlier ranges stay valid. *)
          let eds = List.sort (fun a b -> compare b.s a.s) eds in
          let out =
            List.fold_left
              (fun acc e ->
                incr ne;
                String.sub acc 0 e.s ^ e.repl ^ String.sub acc e.e (String.length acc - e.e))
              src eds
          in
          if out <> src then (write_file f out; incr nf))
        by_file;
      (!ne, !nf)
    in
    if cmd = "locate" then begin
      let all, auto, kept, deferred = scan () in
      report all auto kept deferred;
      let rows =
        all
        @ List.map (fun e -> { e with kind = "DEFERRED"; repl = "" }) deferred
      in
      List.iter
        (fun e -> Printf.printf "%s\t%s:%d\t%s\t%s\n" e.kind e.file e.line e.note (escape e.repl))
        (List.sort (fun a b -> compare (a.file, a.line) (b.file, b.line)) rows)
    end
    else if cmd = "patch" then begin
      (* Loop in-process rather than telling the operator to re-run. A fresh
         invocation re-runs `collect_targets` against the already-patched tree,
         where the curried signatures no longer parse as targets -- so the
         deferred inner sites would silently vanish from the worklist. Here
         `targets` is fixed from round 1 and only the sources are re-read. *)
      let total_e = ref 0 and total_f = ref 0 in
      let rec rounds n prev_deferred =
        if n > 10 then begin
          Printf.eprintf "ABORT: patch did not converge in 10 rounds\n";
          exit 1
        end;
        let all, auto, kept, deferred = scan () in
        Printf.eprintf "-- round %d: " n;
        report all auto kept deferred;
        if kept = [] then
          Printf.eprintf "converged after %d round(s); %d deferred remain\n" (n - 1)
            (List.length deferred)
        else begin
          (* The nesting depth of overlapping edits is finite, so the deferred
             set must shrink. If it does not, the tool is producing an edit it
             cannot make progress on -- stop rather than spin. *)
          if n > 1 && List.length deferred >= prev_deferred then begin
            Printf.eprintf "ABORT: deferred count did not decrease (%d -> %d)\n" prev_deferred
              (List.length deferred);
            exit 1
          end;
          let ne, nf = apply kept in
          total_e := !total_e + ne;
          total_f := !total_f + nf;
          Printf.eprintf "   applied %d edits across %d files\n" ne nf;
          rounds (n + 1) (List.length deferred)
        end
      in
      rounds 1 max_int;
      Printf.eprintf "patched %d edits across %d file-writes total\n" !total_e !total_f
    end
    else
      (Printf.eprintf "usage: curry [targets|locate|patch] [scope] [--with-escalate]\n"; exit 1)
  end
