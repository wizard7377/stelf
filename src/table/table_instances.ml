(* # 1 "src/table/table_instances.sig.ml" *)

(* # 1 "src/table/table_instances.fun.ml" *)

(* # 1 "src/table/table_instances.sml.ml" *)
open! Basis
open String_hash
open Hash_table
open Red_black_tree
open Sparse_array
open Sparse_array2

(* Local compare wrappers to work around Basis order type mismatch *)
let string_compare (x, y) : order =
  if x < y then Less else if x = y then Equal else Greater

let int_compare (x, y) : order =
  if x < y then Less else if x = y then Equal else Greater

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

  let compare = string_compare
end)

module IntRedBlackTree = RedBlackTree (struct
  type nonrec key' = int

  let compare = int_compare
end)

module SparseArray = SparseArray (struct
  module IntTable = IntHashTable
end)

module SparseArray2 = SparseArray2 (struct
  module IntTable = IntHashTable
end)
