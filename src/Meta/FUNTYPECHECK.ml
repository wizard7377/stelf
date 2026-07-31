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

(* # 1 "src/meta/Funtypecheck.sig.ml" *)
open! Basis
open Funprint
open Funsyn
open Statesyn

(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)

module type FUNTYPECHECK = sig
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  val isFor : IntSyn.dctx * FunSyn.for_ -> unit
  val check : FunSyn.pro * FunSyn.for_ -> unit
  val checkSub : FunSyn.lfctx * IntSyn.sub * FunSyn.lfctx -> unit
  val isState : StateSyn.state -> unit
end
