  $ ls
  dune
  main.lf
  stelf.toml
  theorems.lf

  $ stelf check stelf.toml
  note: %sort nat
  note: %term 0  nat
  note: %term S  {_0 nat} nat
  note: %sort nt {_0 nat}
  note: %term nt_z  nt 0
  note: %term nt_s  {X nat} {_0 nt X} nt (S X)
  note: %sort plus {_0 nat} {_1 nat} {_2 nat}
  note: %term p_z  {Y nat} plus 0 Y Y
  note: %term p_s  {X nat} {Y nat} {Z nat} {_0 plus X Y Z} plus (S X) Y (S Z)
  note: %sort acker {_0 nat} {_1 nat} {_2 nat}
  note: %term a_1  {Y nat} acker 0 Y (S Y)
  note: %term a_2  {X nat} {Z nat} {_0 acker X (S 0) Z} acker (S X) 0 Z
  note: %term a_3 
     {X nat} {Zp nat} {Z nat} {Y nat} {_0 acker X Zp Z} {_1 acker (S X) Y Zp}
        acker (S X) (S Y) Z
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "a_1"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "a_2"))   ... 
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "a_3"))   ... 
