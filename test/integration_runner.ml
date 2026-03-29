open! Basis

let () =
  Alcotest.run "stelf integration tests"
    [ ("LF examples", Integration.integration_cases) ]
