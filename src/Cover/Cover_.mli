open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Table
open! Table.Table_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Subordinate
open! Subordinate
open! Modes
open! Modes.Modes_
open! Thm
open! Thm.Thm_
open! Terminate
open! Terminate.Terminate_
open! Index
open! Index.Index_
open! Solvers
open! Solvers.Solvers_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Typecheck
open! Typecheck.Typecheck_
open! Timing
open! Timing.Timing_
open! Unique
open! Unique.Unique_
include module type of COVER

module MakeCover
    (Global : GLOBAL)
    (Whnf : WHNF)
    (Conv : CONV)
    (Abstract : ABSTRACT)
    (Unify : UNIFY)
    (Constraints : CONSTRAINTS)
    (ModeTable : Modetable.MODETABLE)
    (UniqueTable : Modetable.MODETABLE)
    (Index : INDEX)
    (Subordinate : Subordinate.Subordinate_.SUBORDINATE)
    (WorldSyn : Worldcheck_.WORLDSYN)
    (Names : NAMES)
    (Print : PRINT)
    (TypeCheck : TYPECHECK)
    (Timers : Timers.TIMERS) : COVER
(*
  (* must be trailing! Constraints *)
  (*! sharing Whnf.IntSyn = IntSyn' !*)
  (*! sharing Abstract.IntSyn = IntSyn' !*)
  (*! sharing Unify.IntSyn = IntSyn' !*)
  (*! sharing Constraints.IntSyn = IntSyn' !*)
  (*! sharing Index.IntSyn = IntSyn' !*)
  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  (*! sharing Names.IntSyn = IntSyn' !*)
  (*! sharing Print.IntSyn = IntSyn' !*)
  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
*)

module Cover : COVER
module Total : TOTAL.TOTAL
