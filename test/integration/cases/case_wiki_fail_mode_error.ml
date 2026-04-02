

let test_case =
  Regression_case.test ~title:"Expected failure: mode violation"
    ~success:false "examples/wiki_failures/mode_error.cfg"
