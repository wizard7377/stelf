  $ ls
  dune
  main.lf
  stelf.toml

  $ stelf check stelf.toml
  note: %sort bool
  note: %term true  bool
  note: %term false  bool
  note: %sort not {_0 bool} {_1 bool}
  note: %term t  not true false
  note: %term f  not false true
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "t"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "f"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "t"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "f"))   ... 
