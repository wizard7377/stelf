  $ stelf check stelf.toml
  => %sort type
  
  => %sort term
  
  => %term λ {F {_0 term} term} term
  
  => %term @ {F term} {X term} term
  
  => %term 0 term
  
  => %term S term
  
  => %term ⊤ term
  
  => %term -> {A type} {B type} type
  
  => %term unit type
  
  => %term ℕ type
  
  => %sort : {X term} {A type}
  
  => %term 0 0 : ℕ
  
  => %term S %val S : ℕ -> ℕ
  
  => %term ⊤ ⊤ : unit
  
  => %term
    λ
      {X term} {F {_0 term} term} {T type} {U type} {_0 {_0 X : T} F X : U}
        λ ([_1 term] F _1) : T -> U
  
  => %term
    @ {F term} {X term} {T type} {U type} {_0 F : T -> U} {_1 X : T} F @ X : U
  
