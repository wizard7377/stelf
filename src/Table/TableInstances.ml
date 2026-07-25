(* # 1 "src/table/TableInstances.sig.ml" *)

(* # 1 "src/table/TableInstances.fun.ml" *)

(* # 1 "src/table/TableInstances.sml.ml" *)
open Basis
open StringHash
open HashTable
open RedBlackTree
open SparseArray
open SparseArray2

(* Local compare wrappers to work around Basis order type mismatch *)
let string_compare (x, y) : order =
  if x < y then Less else if x = y then Equal else Greater

let int_compare (x, y) : order =
  if x < y then Less else if x = y then Equal else Greater

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

  let compare = string_compare
end)

module IntRedBlackTree = RedBlackTree (struct
  type key' = int

  let compare = int_compare
end)

module SparseArray = SparseArray (struct
  module IntTable = IntHashTable
end)

module SparseArray2 = SparseArray2 (struct
  module IntTable = IntHashTable
end)
