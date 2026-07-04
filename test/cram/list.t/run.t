  $ ls
  dune
  main.lf
  stelf.toml

  $ stelf check stelf.toml
  note: %sort nat
  note: %term 0  nat
  note: %term S  {_0 nat} nat
  note: %sort list
  note: %term nil  list
  note: %term cons  {_0 nat} {_1 list} list
  note: %sort append {_0 list} {_1 list} {_2 list}
  note: %term nil  {L list} append nil L L
  note: %term cons 
     {T list} {L list} {M list} {H nat} {_0 append T L M}
        append (cons H T) L (cons H M)
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "nil"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "cons"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "nil"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "cons"))   ... 
