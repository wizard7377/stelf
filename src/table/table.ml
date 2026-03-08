open! Basis
open String_hash
open Hash_table
open Red_black_tree

module StringHashTable = HashTable (struct
  type nonrec key' = string

  let hash = StringHash.stringHash
  let eq (x__op, y__op) = x__op = y__op
end)

module IntHashTable = HashTable (struct
  type nonrec key' = int

  let hash = function n -> n
  let eq (x__op, y__op) = x__op = y__op
end)

module StringRedBlackTree = RedBlackTree (struct
  type nonrec key' = string

  let compare = String.compare
end)

module IntRedBlackTree = RedBlackTree (struct
  type nonrec key' = int

  let compare = Int.compare
end)

module SparseArray = SparseArray (struct
  module IntTable = IntHashTable
end)

module SparseArray2 = SparseArray2 (struct
  module IntTable = IntHashTable
end)
