open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
include module type of ORDER

module MakeOrder (Order__0 : sig
  module Table : TABLE with type key = int
end) : ORDER

module Order : ORDER
include ORDER
