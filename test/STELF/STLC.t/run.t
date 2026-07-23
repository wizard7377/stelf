  $ stelf check stelf.toml
  note: %sort type
  note: %sort term
  note: %term λ  {F {_0 term} term} term
  note: %term @  {F term} {X term} term
  note: %term 0  term
  note: %term S  term
  note: %term ⊤  term
  note: %term ->  {A type} {B type} type
  note: %term unit  type
  note: %term ℕ  type
  note: %sort : {X term} {A type}
  note: %term 0  0 : ℕ
  note: %term S  S : ℕ -> ℕ
  note: %term ⊤  ⊤ : unit
  note: %term λ 
     {X term} {F {_0 term} term} {T type} {U type} {_0 {_0 X : T} F X : U}
        λ ([_1 term] F _1) : T -> U
  note: %term @ 
     {F term} {X term} {T type} {U type} {_0 F : T -> U} {_1 X : T} F @ X : U
