open! Basis
open! Global.Global_
open! Table.Table_
include module type of ORIGINS

module MakeOrigins (Global : GLOBAL) (Table : TABLE with type key = string) :
  ORIGINS

module Origins : ORIGINS
include ORIGINS
