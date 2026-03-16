(* # 1 "src/domains/domains_.sig.ml" *)

(* # 1 "src/domains/domains_.fun.ml" *)

(* # 1 "src/domains/domains_.sml.ml" *)
open Basis
open Int_inf
open Int_inf.Int_inf_
open Integers_mod
module Integers_ = Integers.Integers (Int_inf_.IntInf)
module Rationals_ = Rationals.Rationals (Integers_)

module IntegersMod7 = IntegersMod (struct
  let p = 7
end)
