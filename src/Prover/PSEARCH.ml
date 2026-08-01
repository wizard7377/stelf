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

(* # 1 "src/prover/Search.sig.ml" *)
open! Basis

(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)

module type SEARCH = sig
  (*! structure IntSyn   : INTSYN !*)
  (*! structure Tomega   : TOMEGA !*)
  module State : State.STATE

  exception Error of string

  val searchEx :
    int -> IntSyn.exp list -> (int -> unit) ->
    unit (*      * (StateSyn.FunSyn.IntSyn.Exp * StateSyn.FunSyn.IntSyn.Sub) *)
end
