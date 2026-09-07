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

(* # 1 "src/meta/Abstract.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open Funtypecheck

(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)

module type MTPABSTRACT = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  type approxFor =
    | Head of IntSyn.dctx * (FunSyn.for_ * IntSyn.sub) * int
    | Block of (IntSyn.dctx * IntSyn.sub * int * IntSyn.dec list) * approxFor

  (* Approximat formula *)
  (* AF ::= F [s] *)
  (*  | (t, G2), AF *)
  val weaken : IntSyn.dctx -> IntSyn.cid -> IntSyn.sub
  val raiseType : IntSyn.dctx -> IntSyn.exp -> IntSyn.exp

  val abstractSub :
    IntSyn.sub
    * StateSyn.tag IntSyn.ctx
    * (IntSyn.dctx * StateSyn.tag IntSyn.ctx)
    * IntSyn.sub
    * StateSyn.tag IntSyn.ctx ->
    (IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.sub

  val abstractSub' :
    IntSyn.dctx -> StateSyn.tag IntSyn.ctx -> IntSyn.sub -> StateSyn.tag IntSyn.ctx ->
    (IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.sub

  val abstractApproxFor : approxFor -> FunSyn.for_
end
