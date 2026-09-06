(* Pass "beginend" -- drop `begin`/`end` around the tail of a let-chain when the
   body is a plain sequence:

     let x = ... in begin A; B; C end   ->   let x = ... in A; B; C

   `in` extends maximally, so the delimiters carry no meaning here.

   There is no AST node to match on: `begin e end` and `(e)` parse identically,
   the keywords leaving no trace. So the intent is the IDENTITY mapper -- a
   correct strip must leave the tree bit-for-bit unchanged once locations are
   erased. That check is the whole safety argument, and it is also what rejects
   the shape this pass would otherwise get wrong:

     begin A end; begin B end

   whose location also starts with `begin` and ends with `end`, but whose
   keywords do not pair with each other.

   Only a `Pexp_sequence` body qualifies. `begin if ... then ... end` and other
   non-sequence uses are left alone, per the spec.

   Subcommands: refactor beginend [locate|patch] [scope] *)

open Parsetree
open Core

let starts_with p s = String.length s >= String.length p && String.sub s 0 (String.length p) = p
let ends_with p s =
  String.length s >= String.length p
  && String.sub s (String.length s - String.length p) (String.length p) = p

(* Column of [i] within its line, i.e. how far the token is indented. *)
let col src i =
  let rec go j = if j <= 0 || src.[j - 1] = '\n' then i - j else go (j - 1) in
  go i

let split_lines s = String.split_on_char '\n' s

(* Re-indent the stripped block.

   The edit range begins at the `begin` keyword, so the indentation already on
   that line stays in the file and is NOT part of the replacement. The first
   emitted line must therefore carry no indent of its own or it lands twice as
   deep; every later line gets the `begin`'s column plus whatever it was indented
   relative to the block. *)
let indent_of ln =
  let n = ref 0 in
  while !n < String.length ln && ln.[!n] = ' ' do incr n done;
  !n

let rstrip t =
  let n = ref (String.length t) in
  while !n > 0 && is_ws t.[!n - 1] do decr n done;
  String.sub t 0 !n

let reflow ~to_col inner =
  match split_lines inner with
  | [] -> inner
  | first :: rest ->
      (* A block written `begin` <newline> ... starts on the next line; one
         written `begin A;` <newline> starts on the `begin` line itself. *)
      let body = if String.trim first = "" then rest else first :: rest in
      let nonblank = List.filter (fun l -> String.trim l <> "") body in
      let base = List.fold_left (fun acc l -> min acc (indent_of l)) max_int nonblank in
      let base = if base = max_int then 0 else base in
      let shift l =
        if String.trim l = "" then ""
        else String.make (to_col + (indent_of l - base)) ' ' ^ String.trim l
      in
      (match body with
      | [] -> ""
      | h :: t -> rstrip (String.concat "\n" (String.trim h :: List.map shift t)))

type site = { s : int; e : int; repl : string; ln : int }

let sites_of src ast =
  let acc = ref [] in
  let it =
    { Ast_iterator.default_iterator with
      expr =
        (fun self ex ->
          (match ex.pexp_desc with
          | Pexp_let (_, _, ({ pexp_desc = Pexp_sequence (a, b); pexp_attributes = []; _ } as body))
            when not body.pexp_loc.loc_ghost ->
              let bs = body.pexp_loc.loc_start.pos_cnum
              and be = body.pexp_loc.loc_end.pos_cnum in
              let t = sub src body.pexp_loc in
              (* Both keywords must lie outside the sequence's own elements.
                 In `begin A end; begin B end` the first element's location
                 already starts at `begin`, so this rejects it cheaply before the
                 verifier has to. *)
              let inside =
                a.pexp_loc.loc_start.pos_cnum > bs + 5 && b.pexp_loc.loc_end.pos_cnum < be - 3
              in
              if starts_with "begin" t && ends_with "end" t && inside && String.length t > 8 then begin
                let inner = String.sub t 5 (String.length t - 8) in
                let repl = reflow ~to_col:(col src bs) inner in
                acc := { s = bs; e = be; repl; ln = body.pexp_loc.loc_start.pos_lnum } :: !acc
              end
          | _ -> ());
          Ast_iterator.default_iterator.expr self ex);
      attribute = (fun _ _ -> ())
    }
  in
  (match ast with Impl st -> it.structure it st | Intf sg -> it.signature it sg);
  List.rev !acc

let classify file src ast =
  let sts = sites_of src ast in
  if sts = [] then []
  else
    let ed st = { file; s = st.s; e = st.e; repl = st.repl; kind = "BEGINEND"; line = st.ln; note = "let ... in begin ... end" } in
    let check eds = verify ~path:file ~src ~original:ast ~intent:Ast_mapper.default_mapper eds in
    let all = List.map ed sts in
    match check (fst (non_overlapping all)) with
    | None -> all
    | Some _ ->
        List.map
          (fun st ->
            match check [ ed st ] with
            | None -> ed st
            | Some why ->
                bump ("decline: " ^ why);
                { (ed st) with kind = "DECLINE"; repl = "" })
          sts

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
    let auto = List.filter (fun e -> e.kind = "BEGINEND") all in
    let kept, deferred = non_overlapping auto in
    (all, auto, kept, deferred)
  in
  let report all auto kept deferred =
    let count k = List.length (List.filter (fun e -> e.kind = k) all) in
    Printf.eprintf "BEGINEND=%d DECLINE=%d | auto=%d kept=%d overlap-deferred=%d\n" (count "BEGINEND")
      (count "DECLINE") (List.length auto) (List.length kept) (List.length deferred);
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
  else (Printf.eprintf "usage: refactor beginend [locate|patch] [scope]\n"; exit 1)
