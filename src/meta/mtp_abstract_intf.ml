(* # 1 "src/meta/abstract.sig.ml" *)
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
  val weaken : IntSyn.dctx * IntSyn.cid -> IntSyn.sub
  val raiseType : IntSyn.dctx * IntSyn.exp -> IntSyn.exp

  val abstractSub :
    IntSyn.sub
    * StateSyn.tag IntSyn.ctx
    * (IntSyn.dctx * StateSyn.tag IntSyn.ctx)
    * IntSyn.sub
    * StateSyn.tag IntSyn.ctx ->
    (IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.sub

  val abstractSub' :
    (IntSyn.dctx * StateSyn.tag IntSyn.ctx)
    * IntSyn.sub
    * StateSyn.tag IntSyn.ctx ->
    (IntSyn.dctx * StateSyn.tag IntSyn.ctx) * IntSyn.sub

  val abstractApproxFor : approxFor -> FunSyn.for_
end
