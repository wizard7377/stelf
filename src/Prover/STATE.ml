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

(* # 1 "src/prover/State.sig.ml" *)
open! Basis

(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

module type STATE = sig
  exception Error of string

  type state =
    | State of Tomega.worlds * Tomega.dec IntSyn.ctx * Tomega.prg * Tomega.for_
    | StateLF of IntSyn.exp

  type focus = Focus of Tomega.prg * Tomega.worlds | FocusLF of IntSyn.exp

  (* Focus (EVar, W) *)
  (* focus EVar *)
  val init : Tomega.for_ -> Tomega.worlds -> state
  val close : state -> bool
  val collectT : Tomega.prg -> Tomega.prg list
  val collectLF : Tomega.prg -> IntSyn.exp list
  val collectLFSub : Tomega.sub -> IntSyn.exp list
end
