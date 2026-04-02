

let test_case =
  Regression_case.test ~title:"Expected failure: unsatisfiable query on empty type"
    ~success:false "examples/wiki_failures/unsatisfiable_query.cfg"
