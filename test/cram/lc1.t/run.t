  $ ls
  dune
  main.lf
  src
  stelf.toml

  $ stelf check stelf.toml
  note: %sort κ
  note: %sort τ
  note: %sort e
  note: %sort : {term0 e} {type0 τ}
  note: %term *  κ
  note: %term =>  {A τ} {B {X e} {_0 : X A} κ} κ
  note: %term @  {kind0 κ} {term0 e} κ
  note: %term ->  {A τ} {B {X e} {_0 : X A} τ} τ
  note: %term Λ  {type0 {term0 e} τ} τ
  note: %term @  {type0 τ} {term0 e} τ
  note: %term λ  {term0 {term0 e} e} e
  note: %term @  {term0 e} {term1 e} e
  note: %sort arity
  note: %term nil  {T τ} arity
  note: %term ->>  {_0 arity} {_1 arity} arity
  note: %sort erase {type0 τ} {_0 arity}
  note: %term @ 
     {A τ} {T arity} {B {term0 e} {_0 : term0 A} τ} {U arity} {_0 erase A T}
        {_1 {X e} {P : X A} erase (B X P) U}
        erase (A -> ([X e] [_2 : X A] B X _2)) U
  note: checking mode of constant   (Names_.MakeNames.Qid ([], "@"))   ... 
