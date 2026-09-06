(* Pass "selftest" -- proves Core's AST verifier is sound before any pass relies
   on it.

   The verifier compares a reparsed tree against an intended one with locations
   erased. If the eraser missed a location field, `erase got = erase want` would
   be false for *every* file, and every pass would silently classify all its work
   as ESCALATE -- a total failure that looks exactly like conservatism working.

   So: verify every file against the identity intent with no edits. A patched
   text identical to the original must reparse to an identical tree. Any failure
   here means the verifier cannot be trusted. *)

open Core

let main _args =
  let files = all_files scan_roots in
  let ok = ref 0 and bad = ref 0 and unparsed = ref 0 in
  List.iter
    (fun f ->
      match parse_file f with
      | exception _ -> incr unparsed
      | src, original -> (
          match verify ~path:f ~src ~original ~intent:Ast_mapper.default_mapper [] with
          | None -> incr ok
          | Some why ->
              incr bad;
              Printf.printf "UNSOUND\t%s\t%s\n" f why))
    files;
  Printf.eprintf "verifier selftest: %d ok, %d unsound, %d unparsable\n" !ok !bad !unparsed;
  if !bad > 0 then begin
    Printf.eprintf "ABORT: the location eraser is incomplete; no pass may rely on verify\n";
    exit 1
  end
