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
include module type of THMPRINT

module ThmPrint (ThmPrint__0 : sig
  module ThmSyn' : Thmsyn.THMSYN
  module Formatter : FORMATTER
end) : THMPRINT with module ThmSyn = ThmPrint__0.ThmSyn'
