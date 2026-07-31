open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Formatter
open! Formatter__Formatter_
open! Modes
open! Modes__Modes_
open! Paths
open! Paths.Paths_
open! Tabling
include module type of THM

module Make_Thm
    (Global : GLOBAL)
    (ThmSyn' : Thmsyn.THMSYN)
    (TabledSyn : Tabledsyn.TABLEDSYN)
    (ModeTable : Modetable.MODETABLE)
    (Order : ORDER)
    (ThmPrint : Thmprint.THMPRINT) : THM with module ThmSyn = ThmSyn'
(*
  (*! sharing Order.IntSyn = ThmSyn'.ModeSyn.IntSyn !*)
*)

module ThmSyn : Thmsyn.THMSYN
module ThmPrint : Thmprint.THMPRINT with module ThmSyn = ThmSyn
module Thm : THM with module ThmSyn = ThmSyn
