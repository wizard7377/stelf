open! Basis

let test_case =
  (* TODO Test that this FAILS *)
  Regression_case.test ~title:"examples/failure/sources.cfg (expected failure)"
    ~success:false "examples/failure/sources.cfg"
