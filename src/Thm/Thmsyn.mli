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
include module type of THMSYN

module ThmSyn (ThmSyn__0 : sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure ModeSyn' : MODESYN !*)
  (*! sharing ModeSyn'.IntSyn = IntSyn !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  (*! structure Paths' : PATHS !*)
  module Names' : NAMES
end) : THMSYN with module Names = ThmSyn__0.Names'
