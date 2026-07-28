  $ stelf check stelf.toml
  => %sort ℕ
  
  => %term 0 ℕ
  
  => %term S {nat0 ℕ} ℕ
  
  => %inline 1 %the ℕ %val S 0
  
  => %inline 2 %the ℕ %val S (%val S 0)
  
  => %sort add {nat0 ℕ} {nat1 ℕ} {nat2 ℕ}
  
  => %term 0 {X ℕ} add %%%0%%% X X
  
  => %term S {X ℕ} {Y ℕ} {Z ℕ} {_0 add X Y Z} add (%%%S%%% X) Y (%%%S%%% Z)
  
  => %sort goal {X ℕ} {_0 add %%%0%%% X X}
  
  => %term case-0 goal %%%0%%% (0 %%%0%%%)
  
  => %term case-S {X ℕ} goal (%%%S%%% X) (0 (%%%S%%% X))
  
  note: checking mode of constant   case-0   ... 
  note: checking mode of constant   case-S   ... 
  note: checking mode of constant   case-0   ... 
  note: checking mode of constant   case-S   ... 
  => %sort mul {nat0 ℕ} {nat1 ℕ} {nat2 ℕ}
  
  => %term 0 {X ℕ} mul X %%%0%%% %%%0%%%
  
  => %term
    S
      {X ℕ} {Y ℕ} {Z ℕ} {Z' ℕ} {_0 mul X Y Z} {_1 add Y Z Z'}
        mul (%%%S%%% X) Y Z'
  

  $ stelf repl stelf.toml
  => %sort ℕ
  
  => %term 0 ℕ
  
  => %term S {nat0 ℕ} ℕ
  
  => %inline 1 %the ℕ %val S 0
  
  => %inline 2 %the ℕ %val S (%val S 0)
  
  => %sort add {nat0 ℕ} {nat1 ℕ} {nat2 ℕ}
  
  => %term 0 {X ℕ} add %%%0%%% X X
  
  => %term S {X ℕ} {Y ℕ} {Z ℕ} {_0 add X Y Z} add (%%%S%%% X) Y (%%%S%%% Z)
  
  => %sort goal {X ℕ} {_0 add %%%0%%% X X}
  
  => %term case-0 goal %%%0%%% (0 %%%0%%%)
  
  => %term case-S {X ℕ} goal (%%%S%%% X) (0 (%%%S%%% X))
  
  debug: checking mode of constant   %case-0%   ... 
  
  debug: checking mode of constant   %case-S%   ... 
  
  debug: checking mode of constant   %case-0%   ... 
  
  debug: checking mode of constant   %case-S%   ... 
  
  => %sort mul {nat0 ℕ} {nat1 ℕ} {nat2 ℕ}
  
  => %term 0 {X ℕ} mul X %%%0%%% %%%0%%%
  
  => %term
    S
      {X ℕ} {Y ℕ} {Z ℕ} {Z' ℕ} {_0 mul X Y Z} {_1 add Y Z Z'}
        mul (%%%S%%% X) Y Z'
  
