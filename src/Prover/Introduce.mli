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
include module type of INTRODUCE

module Introduce (Introduce__0 : sig
  (* Introduce *)
  (* Author: Carsten Schuermann *)
  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module State' : State.STATE
  module TomegaNames : Tomeganames.TOMEGANAMES
end) : INTRODUCE with module State = Introduce__0.State'
