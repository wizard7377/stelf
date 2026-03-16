open! Basis

let test_case =
  Regression_case.test ~unsafe:true ~title:"testUnsafe ../examples/lp/test.cfg"
    "../examples/lp/test.cfg"
