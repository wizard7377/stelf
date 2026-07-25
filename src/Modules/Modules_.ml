(* # 1 "src/modules/Modules_.sig.ml" *)

(* # 1 "src/modules/Modules_.fun.ml" *)

(* # 1 "src/modules/Modules_.sml.ml" *)
open! Basis
open TableInstances

module ModSyn = Modsyn.ModSyn (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  module Names__ = Names

  (*! structure Paths' = Paths !*)
  module Origins = Origins
  module Whnf = Whnf
  module Strict = Strict
  module IntTree = IntRedBlackTree
  module HashTable = StringHashTable
end)
