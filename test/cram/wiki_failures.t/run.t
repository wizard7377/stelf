  $ ls
  coverage_error.lf
  dune
  mode_error.lf
  totality_error.lf
  unsatisfiable_query.lf

  $ stelf check coverage_error.lf
  note: %sort tp
  note: %term int  tp
  note: %term float  tp
  note: %term arrow  {_0 tp} {_1 tp} tp
  note: %sort sub {_0 tp} {_1 tp}
  note: %term sub-ii  sub int int
  note: %term sub-ff  sub float float
  note: %term sub-if  sub int float
  note: %term sub-arrow 
     {S tp} {S' tp} {T' tp} {T tp} {_0 sub S S'} {_1 sub T' T}
        sub (arrow T S) (arrow T' S')
  note: %sort sub-trans {_0 tp} {_1 tp} {_2 tp}
  note: %term sub-trans/refl  {T tp} sub-trans T T T
  note: %term sub-trans/arrow 
     {T3 tp} {T3' tp} {T1' tp} {T1 tp} {_0 sub-trans T3 T3 T3'}
        {_1 sub-trans T1' T1 T1}
        sub-trans (arrow T1 T3) (arrow T1 T3) (arrow T1' T3')
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "sub-trans/refl"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "sub-trans/arrow"))   ... 
  note: Occurrence of variable T1' in input (+) argument not necessarily grounderror: [error] :Occurrence of variable T1' in input (+) argument not necessarily ground
  [1]

  $ stelf check mode_error.lf
  note: %sort nat
  note: %term 0  nat
  note: %term S  {_0 nat} nat
  note: %sort plus {_0 nat} {_1 nat} {_2 nat}
  note: %term plus/z  {N nat} plus 0 N N
  note: %term plus/s 
     {N1 nat} {N2 nat} {N3 nat} {_0 plus N1 N2 N3} plus (S N1) N2 (S N3)
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "plus/z"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "plus/s"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "plus/z"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "plus/s"))   ... 
  note: %sort bad {_0 nat} {_1 nat}
  note: %term bad/case  {N1 nat} {N2 nat} {_0 plus N1 N2 N1} bad N1 N2
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "bad/case"))   ... 
  note: Occurrence of variable N2 in input (+) argument not necessarily grounderror: [error] :Occurrence of variable N2 in input (+) argument not necessarily ground
  [1]

  $ stelf check totality_error.lf
  error: [error] %total: undeclared identifier case in call pattern
  [1]

  $ stelf check unsatisfiable_query.lf
  note: %sort void
  => No solution.
  
