  $ stelf check stelf.toml
  => %sort ℕ
  
  => %term 0 ℕ
  
  => %term S {nat0 ℕ} ℕ
  
  => %inline 1 %the ℕ %val S 0
  
  => %inline 2 %the ℕ %val S (%val S 0)
  
  => %sort add {nat0 ℕ} {nat1 ℕ} {nat2 ℕ}
  
  => %term 0 {X ℕ} add %(nat 0) X X
  
  => %term S {X ℕ} {Y ℕ} {Z ℕ} {_0 add X Y Z} add (%(nat S) X) Y (%(nat S) Z)
  
  => %sort goal {X ℕ} {_0 add %(nat 0) X X}
  
  => %term case-0 goal %(nat 0) (0 %(nat 0))
  
  => %term case-S {X ℕ} goal (%(nat S) X) (0 (%(nat S) X))
  
  note: checking mode of constant   case-0   ... 
  
  note: checking mode of constant   case-S   ... 
  
  note: checking mode of constant   case-0   ... 
  
  note: checking mode of constant   case-S   ... 
  
  => %sort mul {nat0 ℕ} {nat1 ℕ} {nat2 ℕ}
  
  => %term 0 {X ℕ} mul X %(nat 0) %(nat 0)
  
  => %term
    S
      {X ℕ} {Y ℕ} {Z ℕ} {Z' ℕ} {_0 mul X Y Z} {_1 add Y Z Z'}
        mul (%(nat S) X) Y Z'
  

  $ stelf repl stelf.toml
  => %sort ℕ
  
  => %term 0 ℕ
  
  => %term S {nat0 ℕ} ℕ
  
  => %inline 1 %the ℕ %val S 0
  
  => %inline 2 %the ℕ %val S (%val S 0)
  
  => %sort add {nat0 ℕ} {nat1 ℕ} {nat2 ℕ}
  
  => %term 0 {X ℕ} add %(nat 0) X X
  
  => %term S {X ℕ} {Y ℕ} {Z ℕ} {_0 add X Y Z} add (%(nat S) X) Y (%(nat S) Z)
  
  => %sort goal {X ℕ} {_0 add %(nat 0) X X}
  
  => %term case-0 goal %(nat 0) (0 %(nat 0))
  
  => %term case-S {X ℕ} goal (%(nat S) X) (0 (%(nat S) X))
  
  debug: checking mode of constant   %case-0%   ... 
  
  debug: checking mode of constant   %case-S%   ... 
  
  debug: checking mode of constant   %case-0%   ... 
  
  debug: checking mode of constant   %case-S%   ... 
  
  => %sort mul {nat0 ℕ} {nat1 ℕ} {nat2 ℕ}
  
  => %term 0 {X ℕ} mul X %(nat 0) %(nat 0)
  
  => %term
    S
      {X ℕ} {Y ℕ} {Z ℕ} {Z' ℕ} {_0 mul X Y Z} {_1 add Y Z Z'}
        mul (%(nat S) X) Y Z'
  
