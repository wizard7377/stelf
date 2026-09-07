open! Basis
open! Table.Table_
open! Intsyn
include module type of ORDER
module MakeOrder (Table : TABLE with type key = int) : ORDER
module Order : ORDER
include ORDER
