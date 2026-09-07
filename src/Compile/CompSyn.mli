open! Basis
open! Global.Global_
open! Table.Table_
open! Names.Names_
include module type of COMPSYN

module Make_CompSyn
    (Global_ : GLOBAL)
    (Names_ : NAMES)
    (Table_ : TABLE with type key = int) : COMPSYN

module CompSyn : COMPSYN
include COMPSYN
