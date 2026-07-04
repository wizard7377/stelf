  $ ls
  dune
  main.lf
  stelf.toml

  $ stelf check stelf.toml
  note: %sort nat
  note: %term 0  nat
  note: %term S  {_0 nat} nat
  note: %sort add {_0 nat} {_1 nat} {_2 nat}
  note: %term 0  {X nat} add X 0 X
  note: %term S  {X nat} {Y nat} {Z nat} {_0 add X Y Z} add X (S Y) (S Z)
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "0"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "S"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "0"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "S"))   ... 
