open! Basis
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Print
open! Print.Print_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Index
open! Index.Index_
include module type of TABLEDSYN

module MakeTabledSyn
    (Names : NAMES)
    (Table : TABLE with type key = int)
    (Index : INDEX) : TABLEDSYN
(*
  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES
  (*! sharing Names.IntSyn = IntSyn' !*)
  module Table : TABLE with type key = int
  module Index : INDEX
*)
