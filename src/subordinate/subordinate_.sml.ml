open! Basis

module MemoTable = Hash_table.HashTable (struct
  type nonrec key' = int * int

  let hash = function n, m -> (7 * n) + m
  let eq (x__op, y__op) = x__op = y__op
end)

module Subordinate = MakeSubordinate (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Names = Names
  module Table = Table_instances.IntRedBlackTree
  module MemoTable = MemoTable
  module IntSet = Intset.IntSet
end)
