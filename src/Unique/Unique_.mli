open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Subordinate
open! Modes
open! Typecheck.Typecheck_
open! Index.Index_
open! Worldcheck
open! Timing
include module type of UNIQUE

module MakeUnique
    (Global : GLOBAL)
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Unify : UNIFY)
    (Constraints : CONSTRAINTS)
    (UniqueTable : Modetable.MODETABLE)
    (UniqueCheck : Modecheck.MODECHECK)
    (Index : INDEX)
    (Subordinate : Subordinate_.SUBORDINATE)
    (WorldSyn : Worldcheck_.WORLDSYN)
    (Names : NAMES)
    (Print : PRINT)
    (TypeCheck : TYPECHECK)
    (Timers : Timers.TIMERS) : UNIQUE
(* must be trailing: Constraints *)

module UniqueTable : Modetable.MODETABLE
module UniqueCheck : Modecheck.MODECHECK
module Unique : UNIQUE
