open! Basis
open! Global.Global_
open! Table.Table_
include module type of FUNNAMES

module FunNames (FunNames__0 : sig
  module Global : GLOBAL

  (*! structure FunSyn' : FUNSYN !*)
  module HashTable : TABLE with type key = string
end) : FUNNAMES.FUNNAMES
