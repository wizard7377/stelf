

let test_case =
  Regression_case.test ~title:"Expected failure: non-terminating recursion"
    ~success:false "examples/wiki_failures/totality_error.cfg"
