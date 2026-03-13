(* # 1 "src/modules/modules_.sig.ml" *)

(* # 1 "src/modules/modules_.fun.ml" *)

(* # 1 "src/modules/modules_.sml.ml" *)
open! Basis
open Table_instances

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
