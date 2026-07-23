  $ ls
  dune
  main.lf
  stelf.toml

  $ stelf check stelf.toml
  note: %sort nat
  note: %term zero  nat
  note: %term succ  {_0 nat} nat
  note: %sort holds {_0 nat}
  note: %term ok  holds zero
  note: %term zero  nat
  note: %term probe-abs  holds %zero%
  note: %term probe-val  holds zero
  note: %term probe-abs-q  holds zero
  note: %term probe-val-q  holds zero
  note: %term lonely  nat
  note: %term probe-fallback  holds lonely
