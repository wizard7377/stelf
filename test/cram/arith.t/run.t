  $ ls
  dune
  main.lf
  stelf.toml
  theorems.lf

  $ stelf check stelf.toml
  => %sort nat
  
  => %term 0  nat
  
  => %term S  {_0 nat} nat
  
  => %sort nt {_0 nat}
  
  note: ././main.lf:1.151-1.160 Error: 
  Undeclared identifier 0
  warning: Undeclared identifier 0error: [recon] 1.141-1.146 Error: 
   1 error found
  [1]
