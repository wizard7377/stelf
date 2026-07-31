open! Basis
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
include module type of SUBORDINATE

module MakeSubordinate
    (Global : GLOBAL)
    (Whnf : WHNF)
    (Names : NAMES)
    (Table : TABLE with type key = int)
    (MemoTable : TABLE with type key = int * int)
    (IntSet : Intset.INTSET) : SUBORDINATE
(*
  (*! structure IntSyn' : INTSYN !*)
  (*! sharing Whnf.IntSyn = IntSyn' !*)
  (*! sharing Names.IntSyn = IntSyn' !*)
*)

module Subordinate : SUBORDINATE
