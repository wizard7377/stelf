

let test_case =
  Regression_case.test ~title:"Expected failure: incomplete coverage in subtyping"
    ~success:false "examples/wiki_failures/coverage_error.cfg"
