(** Integration test runner for STELF. *)

let () =
  Alcotest.run "stelf integration tests"
    [ ("LF examples", Integration.integration_cases) ]
