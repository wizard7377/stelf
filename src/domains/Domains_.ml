(* # 1 "src/domains/Domains_.sig.ml" *)

(* # 1 "src/domains/Domains_.fun.ml" *)

(* # 1 "src/domains/Domains_.sml.ml" *)
open IntegersMod
module Integers_ = Integers.Integers (IntInf.IntInf_.IntInf)
module Rationals_ = Rationals.Rationals (Integers_)

module IntegersMod7 = IntegersMod (struct
  let p = 7
end)
