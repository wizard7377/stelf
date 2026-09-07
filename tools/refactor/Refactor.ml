(* refactor -- mechanical source-to-source refactoring passes for the SML -> OCaml
   port. One executable, one module per pass, a shared Core.

   Usage: refactor <pass> <targets|locate|patch> [scope-prefix] [--with-escalate]

   Every pass is report-first: `locate` classifies each site and writes a TSV
   report without touching the tree; `patch` applies only the sites it classified
   as automatic. Run from the repository root -- passes filter on the literal
   prefix "src/" and read basis/lib at runtime. *)

let passes = [ ("curry", Pass_curry.main); ("selftest", Pass_selftest.main); ("letunit", Pass_letunit.main); ("beginend", Pass_beginend.main); ("defun", Pass_defun.main) ]

let () =
  match List.tl (Array.to_list Sys.argv) with
  | pass :: rest when List.mem_assoc pass passes -> (List.assoc pass passes) rest
  | pass :: _ ->
      Printf.eprintf "refactor: unknown pass %S (known: %s)\n" pass
        (String.concat ", " (List.map fst passes));
      exit 1
  | [] ->
      Printf.eprintf "usage: refactor <pass> <targets|locate|patch> [scope] [--with-escalate]\n";
      Printf.eprintf "passes: %s\n" (String.concat ", " (List.map fst passes));
      exit 1
