(* # 1 "src/worldcheck/worldcheck_.sig.ml" *)

(* # 1 "src/worldcheck/worldcheck_.fun.ml" *)

(* # 1 "src/worldcheck/worldcheck_.sml.ml" *)
open! Basis

module type WORLDIFY = Worldify.WORLDIFY
module type WORLDSYN = WorldSyn.WORLDSYN

module MemoTable = Hash_table.HashTable (struct
  type key' = int * int

  let hash (n, m) = (7 * n) + m
  let eq (x__op, y__op) = x__op = y__op
end)

module WorldSyn = WorldSyn.WorldSyn (struct
  module Global = Global
  module Whnf = Whnf
  module Names = Names
  module Unify = UnifyTrail
  module Abstract = Abstract
  module Constraints = Constraints
  module Index = Index

  (*! structure Cs_manager = Cs_manager !*)
  module Subordinate = Subordinate_.Subordinate
  module Print = Print
  module Table = Table_instances.IntRedBlackTree
  module Origins = Origins
  module Timers = Timers.Timers
end)

module Worldify = Worldify.Worldify (struct
  module Global = Global

  (*! structure IntSyn = IntSyn !*)
  module WorldSyn = WorldSyn

  (*! structure Tomega = Tomega !*)
  module Whnf = Whnf
  module Names = Names
  module Unify = UnifyTrail
  module Abstract = Abstract
  module Constraints = Constraints
  module Index = Index
  module Cs_manager = Cs_manager
  module Subordinate = Subordinate_.Subordinate
  module Print = Print
  module Table = Table_instances.IntRedBlackTree
  module MemoTable = MemoTable
  module IntSet = Intset.IntSet

  (*! structure Paths = Paths !*)
  module Origins = Origins
end)
