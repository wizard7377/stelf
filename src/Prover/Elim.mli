open! Basis
open! Tomega_lib
open! Tomega_lib.Tomega_
open! Intsyn
open! Intsyn.Lambda_
open! Global
open! Global.Global_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Index
open! Index.Index_
open! Modes
open! Modes.Modes_
open! Typecheck
open! Typecheck.Typecheck_
open! Table
open! Table.Table_
open! Subordinate
open! Subordinate
open! Solvers
open! Solvers.Solvers_
open! Opsem
open! Trail
open! Trail.Trail_
open! Compile
open! Compile.Compile_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Formatter
open! Formatter__Formatter_
open! Timing
open! Timing.Timing_
include module type of ELIM

module Elim (Elim__0 : sig
  module Data : Data.DATA

  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module State' : State.STATE

  (*! sharing State'.IntSyn = IntSyn' !*)
  (*! sharing State'.Tomega = Tomega' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  (*! sharing Abstract.Tomega = Tomega' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY
end) : ELIM with module State = Elim__0.State'
