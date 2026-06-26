  $ ls
  coverage_error.lf
  dune
  mode_error.lf
  totality_error.lf
  unsatisfiable_query.lf

  $ stelf check coverage_error.lf
  [1]

  $ stelf check mode_error.lf
  [1]

  $ stelf check totality_error.lf
  [1]

  $ stelf check unsatisfiable_query.lf
  [1]
