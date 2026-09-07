(* Pass "rename" -- drop the trailing underscore from a local binder where the
   bare name is not in play.

   SML allows capitalised variables, so the port mapped `G` to `g_`, `U` to `u_`
   and so on. Where no bare `g` was ever in play the underscore is pure residue,
   and STYLE.md already asks for it to go.

   The rewrite is a whole-region token substitution over one binder's scope, which
   is sound for a reason worth stating: *within a binder's own scope there is no
   free occurrence of the name it binds*. Every `g_` in the region resolves to
   this binder or to an inner one that shadows it, so renaming all of them at once
   is a bijection on that region -- inner shadowing survives intact, just spelled
   without the underscore. The one thing that can go wrong is capture, and that is
   exactly what the guard rules out: the bare name must appear nowhere in the
   region, so nothing there can already mean something else.

   That guard is load-bearing and the AST verifier does *not* back it. Capture is
   a scoping property; rename the wrong thing and the intent tree and the reparse
   agree perfectly, both wrong. `src/Typecheck/Typecheck_.ml` binds `s_` (a spine)
   and `s` (a substitution) in one pattern -- same type, so even the compiler
   would stay silent. What the verifier does buy is the text-scan errors that are
   easy to make: a hit inside a string literal, a record label, a qualified path.

   Scope decision: local bindings only -- parameters, inner `let`s, match-bound
   variables. Module-level `let x_ =` and `val x_` are out of scope by decision;
   they are also nearly disjoint from the capital-letter residue.

   Subcommands: refactor rename [locate|patch] [scope] [--names=a_,b_] *)

open Parsetree
open Asttypes
open Core

let keywords =
  [ "and"; "as"; "assert"; "asr"; "begin"; "class"; "constraint"; "do"; "done";
    "downto"; "else"; "end"; "exception"; "external"; "false"; "for"; "fun";
    "function"; "functor"; "if"; "in"; "include"; "inherit"; "initializer";
    "land"; "lazy"; "let"; "lor"; "lsl"; "lsr"; "lxor"; "match"; "method"; "mod";
    "module"; "mutable"; "new"; "nonrec"; "object"; "of"; "open"; "or"; "private";
    "rec"; "sig"; "struct"; "then"; "to"; "true"; "try"; "type"; "val";
    "virtual"; "when"; "while"; "with" ]

(* Record fields and other non-value binders that happen to end in `_`. *)
let never = [ "done_" ]

let is_id_char c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_' || c = '\''

(* `x'_` -> `x'` is in scope: the prime is part of the name, and the guard treats
   `g'` exactly as it treats `g`. `x__` is not -- stripping one underscore leaves
   another, so the name was never underscore-residue to begin with. *)
let target n =
  let l = String.length n in
  if l < 2 || n.[l - 1] <> '_' then None
  else
    let base = String.sub n 0 (l - 1) in
    if base = "" || base.[String.length base - 1] = '_' then None
    else if n.[0] < 'a' || n.[0] > 'z' then None
    else if List.mem base keywords || List.mem n never then None
    else Some base

(* ------------------------------------------------------------------ *)
(* Token scan                                                          *)
(* ------------------------------------------------------------------ *)

type tok = { ts : int; te : int; txt : string; dotted : bool }

(* Identifier tokens in [s,e), with comments, string literals, quoted strings and
   character literals recognised and skipped. Comments are skipped rather than
   rewritten: only 4 of 4,160 `g_` occurrences tree-wide sit in one, so there is
   no consistency to buy and a large unreviewable diff to avoid. *)
let scan src s e =
  let n = min e (String.length src) in
  let out = ref [] in
  let rec skip_string i =
    if i >= n then n
    else if src.[i] = '\\' then skip_string (i + 2)
    else if src.[i] = '"' then i + 1
    else skip_string (i + 1)
  and skip_comment i d =
    if i >= n then n
    else if i + 1 < n && src.[i] = '(' && src.[i + 1] = '*' then skip_comment (i + 2) (d + 1)
    else if i + 1 < n && src.[i] = '*' && src.[i + 1] = ')' then
      if d = 1 then i + 2 else skip_comment (i + 2) (d - 1)
    else if src.[i] = '"' then skip_comment (skip_string (i + 1)) d
    else skip_comment (i + 1) d
  in
  let rec go i =
    if i >= n then ()
    else if i + 1 < n && src.[i] = '(' && src.[i + 1] = '*' then go (skip_comment i 0)
    else if src.[i] = '"' then go (skip_string (i + 1))
    else if
      (* {id|...|id} quoted string literal *)
      src.[i] = '{'
      &&
      let rec bar j = j < n && (src.[j] = '|' || (is_id_char src.[j] && bar (j + 1))) in
      let rec fin j = if j < n && src.[j] = '|' then Some (String.sub src (i + 1) (j - i - 1)) else if j < n && is_id_char src.[j] then fin (j + 1) else None in
      bar (i + 1) && fin (i + 1) <> None
    then begin
      let rec fin j = if src.[j] = '|' then String.sub src (i + 1) (j - i - 1) else fin (j + 1) in
      let tag = fin (i + 1) in
      let close = "|" ^ tag ^ "}" in
      let rec find j =
        if j + String.length close > n then n
        else if String.sub src j (String.length close) = close then j + String.length close
        else find (j + 1)
      in
      go (find (i + 1 + String.length tag + 1))
    end
    else if
      (* character literal: 'a' or '\n' -- but not a type variable 'a *)
      src.[i] = '\''
      && ((i + 1 < n && src.[i + 1] = '\\') || (i + 2 < n && src.[i + 2] = '\''))
    then begin
      let rec fin j = if j >= n then n else if src.[j] = '\'' then j + 1 else if src.[j] = '\\' then fin (j + 2) else fin (j + 1) in
      go (fin (i + 1))
    end
    else if is_id_char src.[i] && not (src.[i] >= '0' && src.[i] <= '9') then begin
      let j = ref i in
      while !j < n && is_id_char src.[!j] do incr j done;
      out := { ts = i; te = !j; txt = String.sub src i (!j - i); dotted = i > 0 && src.[i - 1] = '.' } :: !out;
      go !j
    end
    else if src.[i] >= '0' && src.[i] <= '9' then begin
      let j = ref i in
      while !j < n && (is_id_char src.[!j] || src.[!j] = '.') do incr j done;
      go !j
    end
    else go (i + 1)
  in
  go s;
  List.rev !out

(* ------------------------------------------------------------------ *)
(* Sites                                                               *)
(* ------------------------------------------------------------------ *)

(* A binder and the byte range its name governs. The range is the *rewrite*
   region as well as the guard region, and is always a superset of the true
   scope, never a subset: it starts at the binder's own pattern (so the binding
   occurrence is renamed too) and runs to the end of the construct. A superset
   only makes the guard stricter, and the extra text holds binding positions, not
   free uses. *)
type site = { name : string; nu : string; s : int; e : int; ln : int }

let pat_binders p =
  let acc = ref [] in
  let it =
    { Ast_iterator.default_iterator with
      pat =
        (fun self p ->
          (match p.ppat_desc with
          | Ppat_var v -> acc := (v.txt, v.loc) :: !acc
          | Ppat_alias (_, v) -> acc := (v.txt, v.loc) :: !acc
          | _ -> ());
          Ast_iterator.default_iterator.pat self p)
    }
  in
  it.pat it p;
  List.rev !acc

let sites_of ast =
  let acc = ref [] in
  let add_pat p (s, e) =
    List.iter
      (fun (n, (l : Location.t)) ->
        match target n with
        | Some nu when not l.loc_ghost ->
            let s = min s l.loc_start.pos_cnum in
            if s < e then acc := { name = n; nu; s; e; ln = l.loc_start.pos_lnum } :: !acc
        | _ -> ())
      (pat_binders p)
  in
  let it =
    { Ast_iterator.default_iterator with
      expr =
        (fun self ex ->
          (match ex.pexp_desc with
          | Pexp_let (rf, vbs, body) ->
              let e = body.pexp_loc.loc_end.pos_cnum in
              let s =
                if rf = Recursive then
                  List.fold_left (fun a vb -> min a vb.pvb_expr.pexp_loc.loc_start.pos_cnum) e vbs
                else body.pexp_loc.loc_start.pos_cnum
              in
              List.iter (fun vb -> add_pat vb.pvb_pat (s, e)) vbs
          | Pexp_function (params, _, _) ->
              let e = ex.pexp_loc.loc_end.pos_cnum in
              List.iter
                (fun p ->
                  match p.pparam_desc with
                  | Pparam_val (_, _, pat) -> add_pat pat (p.pparam_loc.loc_start.pos_cnum, e)
                  | Pparam_newtype _ -> ())
                params
          | Pexp_for (pat, _, _, _, _) -> add_pat pat (ex.pexp_loc.loc_start.pos_cnum, ex.pexp_loc.loc_end.pos_cnum)
          | _ -> ());
          Ast_iterator.default_iterator.expr self ex);
      case =
        (fun self c ->
          add_pat c.pc_lhs (c.pc_lhs.ppat_loc.loc_start.pos_cnum, c.pc_rhs.pexp_loc.loc_end.pos_cnum);
          Ast_iterator.default_iterator.case self c);
      attribute = (fun _ _ -> ())
    }
  in
  (match ast with Impl st -> it.structure it st | Intf sg -> it.signature it sg);
  List.rev !acc

(* ------------------------------------------------------------------ *)
(* Intent                                                             *)
(* ------------------------------------------------------------------ *)

(* Only value identifiers and value binders move. A record label, a type
   constructor or a qualified path that the token scan mistook for a use will
   diverge from this and land as ESCALATE, which is the point of running it. *)
let intent (regions : site list) =
  let hit name (l : Location.t) =
    List.exists
      (fun r -> r.name = name && l.loc_start.pos_cnum >= r.s && l.loc_end.pos_cnum <= r.e)
      regions
  in
  let nu name = (List.find (fun r -> r.name = name) regions).nu in
  let open Ast_mapper in
  { default_mapper with
    expr =
      (fun self ex ->
        match ex.pexp_desc with
        | Pexp_ident ({ txt = Longident.Lident n; loc } as lid) when hit n loc ->
            { ex with pexp_desc = Pexp_ident { lid with txt = Longident.Lident (nu n) } }
        | _ -> default_mapper.expr self ex);
    pat =
      (fun self p ->
        match p.ppat_desc with
        | Ppat_var v when hit v.txt v.loc -> { p with ppat_desc = Ppat_var { v with txt = nu v.txt } }
        | Ppat_alias (q, v) when hit v.txt v.loc ->
            { p with ppat_desc = Ppat_alias (self.pat self q, { v with txt = nu v.txt }) }
        | _ -> default_mapper.pat self p)
  }

(* ------------------------------------------------------------------ *)
(* Classification                                                      *)
(* ------------------------------------------------------------------ *)

let overlaps a b = a.s < b.e && b.s < a.e

let classify ~names file src ast =
  let all = sites_of ast in
  let all = match names with [] -> all | ns -> List.filter (fun r -> List.mem r.name ns) all in
  (* Guard, then drop sites nested inside an accepted site of the same name --
     keyed on accepted sites only, so an inner site still stands when the outer
     one declined. *)
  let accepted, declines =
    List.fold_left
      (fun (acc, dec) r ->
        let toks = scan src r.s r.e in
        if List.exists (fun t -> t.txt = r.nu && not t.dotted) toks then
          (acc, (r, "the bare name is live in this binder's scope") :: dec)
        else if List.exists (fun a -> a.name = r.name && a.s <= r.s && r.e <= a.e) acc then (acc, dec)
        else if List.exists (fun a -> a.name = r.name && overlaps a r) acc then
          (acc, (r, "scope partially overlaps an accepted site of the same name") :: dec)
        else (r :: acc, dec))
      ([], [])
      (List.sort (fun a b -> compare (a.e - a.s, a.s) (b.e - b.s, b.s)) all |> List.rev)
  in
  List.iter (fun (_, why) -> bump ("decline: " ^ why)) declines;
  let dec_rows =
    List.map
      (fun (r, why) -> { file; s = 0; e = 0; repl = ""; kind = "DECLINE"; line = r.ln; note = r.name ^ " -- " ^ why })
      declines
  in
  if accepted = [] then dec_rows
  else
    let eds_of r =
      scan src r.s r.e
      |> List.filter (fun t -> t.txt = r.name && not t.dotted)
      |> List.map (fun t ->
             { file; s = t.ts; e = t.te; repl = r.nu; kind = "RENAME"; line = r.ln; note = r.name ^ " -> " ^ r.nu })
    in
    let check group =
      verify ~path:file ~src ~original:ast ~intent:(intent group) (List.concat_map eds_of group)
    in
    dec_rows
    @
    match check accepted with
    | None -> List.concat_map eds_of accepted
    | Some _ ->
        List.concat_map
          (fun r ->
            match check [ r ] with
            | None -> eds_of r
            | Some why ->
                bump ("decline: " ^ why);
                [ { file; s = 0; e = 0; repl = ""; kind = "ESCALATE"; line = r.ln; note = r.name ^ " -- " ^ why } ])
          accepted

let applied_kinds = [ "RENAME" ]

let main args =
  let names =
    List.concat_map
      (fun a ->
        if String.length a > 8 && String.sub a 0 8 = "--names=" then
          String.split_on_char ',' (String.sub a 8 (String.length a - 8))
        else [])
      args
  in
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
  let scan_tree () =
    edits := [];
    Hashtbl.reset diag;
    List.iter
      (fun f ->
        match parse_file f with
        | exception e -> Printf.eprintf "PARSE FAIL %s: %s\n" f (Printexc.to_string e)
        | src, ast -> List.iter add (classify ~names f src ast))
      files;
    let all = !edits in
    let auto = List.filter (fun e -> List.mem e.kind applied_kinds) all in
    let kept, deferred = non_overlapping auto in
    (all, auto, kept, deferred)
  in
  let report all auto kept deferred =
    let count k = List.length (List.filter (fun e -> e.kind = k) all) in
    Printf.eprintf "RENAME=%d DECLINE=%d ESCALATE=%d | auto=%d kept=%d overlap-deferred=%d\n"
      (count "RENAME") (count "DECLINE") (count "ESCALATE") (List.length auto) (List.length kept)
      (List.length deferred);
    Hashtbl.fold (fun k v acc -> (k, v) :: acc) diag [] |> List.sort compare
    |> List.iter (fun (k, v) -> Printf.eprintf "  %-62s %5d\n" k v)
  in
  if cmd = "locate" then begin
    let all, auto, kept, deferred = scan_tree () in
    report all auto kept deferred;
    List.iter
      (fun e -> Printf.printf "%s\t%s:%d\t%s\n" e.kind e.file e.line e.note)
      (List.sort (fun a b -> compare (a.file, a.line) (b.file, b.line)) all)
  end
  else if cmd = "patch" then begin
    let all, auto, kept, deferred = scan_tree () in
    report all auto kept deferred;
    if kept <> [] then begin
      let ne, nf = apply kept in
      Printf.eprintf "patched %d edits across %d files\n" ne nf
    end
  end
  else (Printf.eprintf "usage: refactor rename [locate|patch] [scope] [--names=a_,b_]\n"; exit 1)
