open! Basis

module MemoTable = HashTable (struct
  type nonrec key' = int * int

  let hash = function n, m -> (7 * n) + m
  let eq (x__op, y__op) = x__op = y__op
end)

module WorldSyn = WorldSyn (struct
  module Global = Global
  module Whnf = Whnf
  module Names = Names
  module Unify = UnifyTrail
  module Abstract = Abstract
  module Constraints = Constraints
  module Index = Index

  (*! structure Cs_manager = Cs_manager !*)
  module Subordinate = Subordinate
  module Print = Print
  module Table = IntRedBlackTree
  module Paths = Paths
  module Origins = Origins
  module Timers = Timers
end)

module Worldify = Worldify (struct
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
  module Subordinate = Subordinate
  module Print = Print
  module Table = IntRedBlackTree
  module MemoTable = MemoTable
  module IntSet = IntSet

  (*! structure Paths = Paths !*)
  module Origins = Origins
end)
