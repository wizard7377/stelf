open! Global.Global_
open! Table
open! Intsyn.Lambda_
open! Names.Names_
open! Paths
open! Typecheck.Typecheck_

(* # 1 "src/modules/Modules_.sig.ml" *)

(* # 1 "src/modules/Modules_.fun.ml" *)

(* # 1 "src/modules/Modules_.sml.ml" *)
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
