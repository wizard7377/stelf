open! Basis

let test_case =
  (* TODO Test that this FAILS *)
  Regression_case.test ~title:"test ../examples/failure/failure.cfg"
    ~success:false "../examples/failure/sources.cfg"
