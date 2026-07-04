  $ ls
  dune
  main.lf
  theorems.lf

  $ stelf check main.lf
  note: %sort o
  note: %sort atm
  note: %term =>  {_0 o} {_1 o} o
  note: %term &  {_0 o} {_1 o} o
  note: %term true  o
  note: %term `  {_0 atm} o
  note: %sort !^ {_0 o}
  note: %sort !v {_0 o}
  note: %term trueI^  !^ true
  note: %term andI^  {B o} {A o} {_0 !^ B} {_1 !^ A} !^ (A & B)
  note: %term impI^  {A o} {B o} {_0 {_0 !v A} !^ B} !^ (A => B)
  note: %term close  {P atm} {_0 !v (` P)} !^ (` P)
  note: %term andEvL  {A o} {B o} {_0 !v (A & B)} !v A
  note: %term andEvR  {A o} {B o} {_0 !v (A & B)} !v B
  note: %term impEv  {A o} {B o} {_0 !^ A} {_1 !v (A => B)} !v B
