(* Pass "letunit" -- `let _ = e in body` becomes `ignore e; body`.

   The SML sequencing idiom came over verbatim. In OCaml it discards a value
   silently rather than saying so, and `ignore` accepts any type, so no type
   information is needed to make the change.

   Two output forms, both sanctioned:

     ignore e; body            preferred
     let () = ignore e in body fallback

   The fallback exists because the sequence form can reassociate. Under
   `if c then let _ = e in body` it yields `(if c then ignore e); body`, which
   still typechecks whenever the `if` has no `else` -- `if c then ignore e` is
   already unit -- and then runs `body` unconditionally. The compiler cannot
   catch that; Core.verify can. The fallback is a `Pexp_let` exactly like the
   original and carries no such risk.

   Subcommands: refactor letunit [locate|patch] [scope] *)

open Parsetree
open Asttypes
open Core

module ISet = Set.Make (Int)

(* A site: the `let` node's start offset keys it, since that is what both the
   text edit and the intent mapper anchor on. *)
type site = { off : int; s : int; e : int; rhs : string; tail : string; ln : int }

let pat_end_of ex =
  match ex.pexp_desc with
  | Pexp_let (_, [ vb ], _) -> vb.pvb_pat.ppat_loc.loc_start.pos_cnum
  | _ -> -1

let sites_of src ast =
  let acc = ref [] in
  let it =
    { Ast_iterator.default_iterator with
      expr =
        (fun self ex ->
          (match ex.pexp_desc with
          | Pexp_let
              ( Nonrecursive,
                [ { pvb_pat = { ppat_desc = Ppat_any; ppat_attributes = []; _ };
                    pvb_expr = rhs; pvb_attributes = []; pvb_constraint = None; _ } ],
                body )
            when ex.pexp_attributes = [] ->
              let st = ex.pexp_loc.loc_start.pos_cnum in
              let bs = body.pexp_loc.loc_start.pos_cnum in
              let rs = rhs.pexp_loc.loc_start.pos_cnum
              and re = rhs.pexp_loc.loc_end.pos_cnum in
              (* `st` is the node key, NOT a text anchor. OCaml's parser folds
                 enclosing parentheses into a parenthesised expression's
                 pexp_loc, so for

                   | p -> (
                       let _ = e in body)

                 loc_start is the '(' and not the `let`. Splicing from there eats
                 the opening paren and orphans its partner. Anchor on the pattern
                 instead: `_` always begins one keyword after `let`, so stepping
                 back over whitespace must land on "let" -- and if it does not,
                 this is a shape we do not understand and decline. *)
              let pe = pat_end_of ex in
              let lk = skip_ws_back src (pe - 1) - 2 in
              let anchored = lk >= 0 && lk + 3 <= String.length src && String.sub src lk 3 = "let" in
              (* Keep the whitespace run that precedes the body, so a multi-line
                 binding does not collapse onto one line. *)
              let ws = skip_ws_back src (bs - 1) + 1 in
              (* Anything between the rhs and `in` -- comments, notably -- is
                 carried through verbatim rather than replaced away. Splicing the
                 whole span silently deleted a comment in Compress_.ml. The `in`
                 must be exactly the two bytes ending the span; when a comment
                 sits between `in` and the body instead, it is not, and we
                 decline rather than guess. *)
              let in_at = ws - 2 in
              let is_in = in_at >= re && String.sub src in_at 2 = "in" in
              if
                anchored && is_in
                && (not ex.pexp_loc.loc_ghost) && (not rhs.pexp_loc.loc_ghost)
                && (not body.pexp_loc.loc_ghost)
                && lk < rs && rs <= re && re <= in_at && ws <= bs
              then
                acc :=
                  Ok { off = st; s = lk; e = ws; rhs = sub src rhs.pexp_loc;
                       tail = String.sub src re (in_at - re);
                       ln = ex.pexp_loc.loc_start.pos_lnum }
                  :: !acc
              else
                acc :=
                  Error
                    ( ex.pexp_loc.loc_start.pos_lnum,
                      if not anchored then "no `let` keyword before the pattern"
                      else if not is_in then "no bare `in` closing the binding"
                      else "unexpected location layout" )
                  :: !acc
          | _ -> ());
          Ast_iterator.default_iterator.expr self ex);
      attribute = (fun _ _ -> ())
    }
  in
  (match ast with Impl st -> it.structure it st | Intf sg -> it.signature it sg);
  List.rev !acc

(* --- the two output forms ------------------------------------------- *)

(* `begin e end` delimits an expression exactly as parens do, and the node's
   location includes both keywords, so a rhs spelled that way already stands
   alone as an argument. Wrapping it again gives `ignore (begin .. end)`. *)
let delimited t =
  let t = String.trim t in
  String.length t > 8 && String.sub t 0 5 = "begin" && String.sub t (String.length t - 3) 3 = "end"

let opener st = if is_atom st.rhs || delimited st.rhs then ("", "") else ("(", ")")

let rstrip t =
  let n = ref (String.length t) in
  while !n > 0 && is_ws t.[!n - 1] do decr n done;
  String.sub t 0 !n

let kept_tail st = if String.trim st.tail = "" then "" else rstrip st.tail

let seq_repl st =
  let o, c = opener st in
  "ignore " ^ o ^ String.trim st.rhs ^ kept_tail st ^ c ^ ";"

let bind_repl st =
  let o, c = opener st in
  "let () = ignore " ^ o ^ String.trim st.rhs ^ kept_tail st ^ c ^ " in"

let edit_of file kind repl st =
  { file; s = st.s; e = st.e; repl = repl st; kind; line = st.ln; note = "let _ =" }

(* --- intent ---------------------------------------------------------- *)

let mknoloc txt = { Location.txt; loc = Location.none }
let ignore_of rhs =
  Ast_helper.Exp.apply (Ast_helper.Exp.ident (mknoloc (Longident.Lident "ignore"))) [ (Nolabel, rhs) ]

(* `body` is carried through untouched, so when it is itself a sequence the
   result nests to the right -- exactly how `ignore e; a; b` parses. Building the
   expectation this way makes the associativity correct by construction rather
   than by a rule someone has to remember. *)
let intent ~seq ~bind =
  let open Ast_mapper in
  { default_mapper with
    expr =
      (fun self ex ->
        match ex.pexp_desc with
        | Pexp_let (Nonrecursive, [ ({ pvb_pat = { ppat_desc = Ppat_any; _ }; _ } as vb) ], body)
          when ISet.mem ex.pexp_loc.loc_start.pos_cnum seq
               || ISet.mem ex.pexp_loc.loc_start.pos_cnum bind ->
            let rhs = self.expr self vb.pvb_expr and body = self.expr self body in
            if ISet.mem ex.pexp_loc.loc_start.pos_cnum seq then
              Ast_helper.Exp.sequence (ignore_of rhs) body
            else
              Ast_helper.Exp.let_ Nonrecursive
                [ Ast_helper.Vb.mk (Ast_helper.Pat.construct (mknoloc (Longident.Lident "()")) None)
                    (ignore_of rhs) ]
                body
        | _ -> default_mapper.expr self ex)
  }

(* --- per-file classification ----------------------------------------- *)

(* Try the whole file in sequence form first; that is one reparse for the common
   case where nothing reassociates. Only a file that fails pays the per-site
   cost of finding which site is responsible. *)
let classify file src ast =
  let raw = sites_of src ast in
  let declines =
    List.filter_map
      (function
        | Error (ln, why) ->
            bump ("decline: " ^ why);
            Some { file; s = 0; e = 0; repl = ""; kind = "DECLINE"; line = ln; note = "let _ = -- " ^ why }
        | Ok _ -> None)
      raw
  in
  let sts = List.filter_map (function Ok st -> Some st | Error _ -> None) raw in
  declines
  @
  if sts = [] then []
  else
    let check seq bind eds =
      verify ~path:file ~src ~original:ast
        ~intent:(intent ~seq:(ISet.of_list seq) ~bind:(ISet.of_list bind))
        eds
    in
    let all_seq = List.map (fun st -> edit_of file "LETUNIT" seq_repl st) sts in
    match check (List.map (fun s -> s.off) sts) [] all_seq with
    | None -> all_seq
    | Some _ ->
        (* Isolate: classify each site on its own, preferring the sequence form
           and falling back to the binding form before giving up. *)
        List.filter_map
          (fun st ->
            let seq_ed = edit_of file "LETUNIT" seq_repl st in
            match check [ st.off ] [] [ seq_ed ] with
            | None -> Some seq_ed
            | Some _ -> (
                let bind_ed = edit_of file "LETUNITBIND" bind_repl st in
                match check [] [ st.off ] [ bind_ed ] with
                | None ->
                    bump "letunit: sequence form would reassociate; used `let () = ignore`";
                    Some bind_ed
                | Some why ->
                    (match Sys.getenv_opt "REFACTOR_DUMP" with
                    | Some dir ->
                        let base = Filename.basename file ^ "." ^ string_of_int st.ln ^ ".dump" in
                        write_file (Filename.concat dir base) (splice src [ seq_ed ])
                    | None -> ());
                    bump ("decline: " ^ why);
                    Some { bind_ed with kind = "ESCALATE"; repl = ""; note = "let _ = -- " ^ why }))
          sts

let applied_kinds = [ "LETUNIT"; "LETUNITBIND" ]

let main args =
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
        | src, ast -> List.iter add (classify f src ast))
      files;
    let all = !edits in
    let auto = List.filter (fun e -> List.mem e.kind applied_kinds) all in
    let kept, deferred = non_overlapping auto in
    (all, auto, kept, deferred)
  in
  let report all auto kept deferred =
    let count k = List.length (List.filter (fun e -> e.kind = k) all) in
    Printf.eprintf "LETUNIT=%d LETUNITBIND=%d ESCALATE=%d | auto=%d kept=%d overlap-deferred=%d\n"
      (count "LETUNIT") (count "LETUNITBIND") (count "ESCALATE") (List.length auto)
      (List.length kept) (List.length deferred);
    Hashtbl.fold (fun k v acc -> (k, v) :: acc) diag []
    |> List.sort compare
    |> List.iter (fun (k, v) -> Printf.eprintf "  %-56s %5d\n" k v)
  in
  if cmd = "locate" then begin
    let all, auto, kept, deferred = scan () in
    report all auto kept deferred;
    List.iter
      (fun e -> Printf.printf "%s\t%s:%d\t%s\t%s\n" e.kind e.file e.line e.note (escape e.repl))
      (List.sort (fun a b -> compare (a.file, a.line) (b.file, b.line)) all)
  end
  else if cmd = "patch" then begin
    (* `let _ = (let _ = e in ()) in body` nests, so the inner site overlaps the
       outer one and is deferred. Unlike curry, re-scanning is sound here: the
       inner `let _` is still a `let _` in the rewritten text, so it is simply
       found again. Loop until a round has nothing left to do. *)
    let total_e = ref 0 and total_f = ref 0 in
    let rec rounds n =
      if n > 10 then (Printf.eprintf "ABORT: patch did not converge in 10 rounds\n"; exit 1);
      let all, auto, kept, deferred = scan () in
      Printf.eprintf "-- round %d: " n;
      report all auto kept deferred;
      if kept <> [] then begin
        let ne, nf = apply kept in
        total_e := !total_e + ne;
        total_f := !total_f + nf;
        Printf.eprintf "   applied %d edits across %d files\n" ne nf;
        rounds (n + 1)
      end
    in
    rounds 1;
    Printf.eprintf "patched %d edits across %d file-writes total\n" !total_e !total_f
  end
  else (Printf.eprintf "usage: refactor letunit [locate|patch] [scope]\n"; exit 1)
