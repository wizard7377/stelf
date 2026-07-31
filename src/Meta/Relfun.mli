open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Subordinate
open! Subordinate
open! Modes
open! Modes.Modes_
open! Typecheck
open! Typecheck.Typecheck_
open! Index
open! Index.Index_
open! Opsem
open! Opsem.Opsem_
open! Compile
open! Compile.Compile_
open! Heuristic
open! Heuristic.Heuristic_
open! Timing
open! Timing.Timing_
open! Solvers
open! Solvers.Solvers_
open! M2
open! M2.M2_
include module type of RELFUN

module RelFun (RelFun__0 : sig
  (* Converter from relational representation to a functional
   representation of proof terms *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure FunSyn' : FUNSYN !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing ModeSyn.IntSyn = FunSyn'.IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = FunSyn'.IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = FunSyn'.IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = FunSyn'.IntSyn !*)
  module Weaken : WEAKEN.WEAKEN

  (*! sharing Weaken.IntSyn = FunSyn'.IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = FunSyn'.IntSyn !*)
  module FunWeaken : FUNWEAKEN.FUNWEAKEN

  (*! sharing FunWeaken.FunSyn = FunSyn' !*)
  module FunNames : FUNNAMES.FUNNAMES
end) : RELFUN.RELFUN
