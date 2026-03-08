open! Basis
open Integers_mod
module Integers_ = Integers.Integers (Int_inf_.IntInf)
module Rationals_ = Rationals.Rationals (Integers_)

module IntegersMod7 = IntegersMod (struct
  let p = 7
end)
