open! Basis

(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)
module type MTPABSTRACT = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  type approxFor_ =
    | Head of IntSyn.dctx * (FunSyn.for_ * IntSyn.sub_) * int
    | Block of (IntSyn.dctx * IntSyn.sub_ * int * IntSyn.dec_ list) * approxFor_

  (* Approximat formula *)
  (* AF ::= F [s] *)
  (*  | (t, G2), AF *)
  val weaken : IntSyn.dctx * IntSyn.cid -> IntSyn.sub_
  val raiseType : IntSyn.dctx * IntSyn.exp_ -> IntSyn.exp_

  val abstractSub :
    IntSyn.sub_
    * StateSyn.tag_ IntSyn.ctx_
    * (IntSyn.dctx * StateSyn.tag_ IntSyn.ctx_)
    * IntSyn.sub_
    * StateSyn.tag_ IntSyn.ctx_ ->
    (IntSyn.dctx * StateSyn.tag_ IntSyn.ctx_) * IntSyn.sub_

  val abstractSub' :
    (IntSyn.dctx * StateSyn.tag_ IntSyn.ctx_)
    * IntSyn.sub_
    * StateSyn.tag_ IntSyn.ctx_ ->
    (IntSyn.dctx * StateSyn.tag_ IntSyn.ctx_) * IntSyn.sub_

  val abstractApproxFor : approxFor_ -> FunSyn.for_
end
(* signature MTPABSTRACT *)
