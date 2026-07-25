open Basis
open String_hash
open HashTable
open RedBlackTree

module StringHashTable = HashTable (struct
  type key' = string

  let hash = StringHash.stringHash
  let eq (x__op, y__op) = x__op = y__op
end)

module IntHashTable = HashTable (struct
  type key' = int

  let hash n = n
  let eq (x__op, y__op) = x__op = y__op
end)

module StringRedBlackTree = RedBlackTree (struct
  type key' = string

  let compare = String.compare
end)

module IntRedBlackTree = RedBlackTree (struct
  type key' = int

  let compare = Int.compare
end)

module SparseArray = SparseArray (struct
  module IntTable = IntHashTable
end)

module SparseArray2 = SparseArray2 (struct
  module IntTable = IntHashTable
end)
