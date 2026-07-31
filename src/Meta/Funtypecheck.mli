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
include module type of FUNTYPECHECK

module FunTypeCheck (FunTypeCheck__0 : sig
  (* Type checking for functional proof term calculus *)
  (* Author: Carsten Schuermann *)
  (*! structure FunSyn' : FUNSYN !*)
  module StateSyn' : STATESYN.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = FunSyn'.IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = FunSyn'.IntSyn !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = FunSyn'.IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = FunSyn'.IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = FunSyn'.IntSyn !*)
  module Subordinate : Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = FunSyn'.IntSyn !*)
  module Weaken : WEAKEN.WEAKEN

  (*! sharing Weaken.IntSyn = FunSyn'.IntSyn   !*)
  module FunPrint : FUNPRINT.FUNPRINT
end) : FUNTYPECHECK.FUNTYPECHECK
