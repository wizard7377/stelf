  $ stelf check stelf.toml
  note: %sort tp
  note: %term =>  {_0 tp} {_1 tp} tp
  note: %term all  {_0 {_0 tp} tp} tp
  note: %sort tm {_0 tp}
  note: %term lam  {A tp} {B tp} {_0 {_0 tm A} tm B} tm (A => B)
  note: %term app  {A tp} {B tp} {_0 tm A} {_1 tm (A => B)} tm B
  note: %term tlam  {A {_0 tp} tp} {_ tp} {_0 {_0 tp} tm (A _)} tm (all ([_1 tp] A _1))
  note: %term tapp  {A {_0 tp} tp} {B tp} {_0 tm (all ([_0 tp] A _0))} tm (A B)

