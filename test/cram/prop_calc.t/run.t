  $ ls
  dune
  equiv.lf
  main.lf

  $ stelf check main.lf
  note: %sort o
  note: %term =>  {_0 o} {_1 o} o
  note: %term &  {_0 o} {_1 o} o
  note: %term true  o
  note: %sort |- {_0 o}
  note: %term K  {A o} {B o} |- (A => B => A)
  note: %term S  {A o} {B o} {C o} |- ((A => B => C) => (A => B) => A => C)
  note: %term ONE  |- true
  note: %term PAIR  {A o} {B o} |- (A => B => A & B)
  note: %term LEFT  {A o} {B o} |- (A & B => A)
  note: %term RIGHT  {A o} {B o} |- (A & B => B)
  note: %term MP  {A o} {B o} {_0 |- A} {_1 |- (A => B)} |- B
  note: %sort ! {_0 o}
  note: %term trueI  ! true
  note: %term andI  {B o} {A o} {_0 ! B} {_1 ! A} ! (A & B)
  note: %term andEL  {A o} {B o} {_0 ! (A & B)} ! A
  note: %term andER  {A o} {B o} {_0 ! (A & B)} ! B
  note: %term impliesI  {A o} {B o} {_0 {_0 ! A} ! B} ! (A => B)
  note: %term impliesE  {A o} {B o} {_0 ! A} {_1 ! (A => B)} ! B
  note: %sort !^ {_0 o}
  note: %sort !v {_0 o}
  note: %term trueI^  !^ true
  note: %term andI^  {B o} {A o} {_0 !^ B} {_1 !^ A} !^ (A & B)
  note: %term impI^  {A o} {B o} {_0 {_0 !v A} !^ B} !^ (A => B)
  note: %term close  {A o} {_0 !v A} !^ A
  note: %term andEvL  {A o} {B o} {_0 !v (A & B)} !v A
  note: %term andEvR  {A o} {B o} {_0 !v (A & B)} !v B
  note: %term impEv  {A o} {B o} {_0 !^ A} {_1 !v (A => B)} !v B
