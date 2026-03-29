open! Basis

let test_case =
  Regression_case.test ~title:"Expected failure: unsatisfiable query"
    ~success:false "examples/failure/sources.cfg"
