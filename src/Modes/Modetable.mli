open! Basis
open! Table.Table_
include module type of MODETABLE
module MakeModeTable (Table : TABLE with type key = int) : MODETABLE
