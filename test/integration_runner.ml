(** Integration test runner for STELF. *)

let () =
  Debug.setup_log ~level:Logs.Debug ();
  Alcotest.run "stelf integration tests"
    [ ("LF examples", Integration.integration_cases) ]
