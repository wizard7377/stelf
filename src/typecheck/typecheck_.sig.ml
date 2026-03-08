open! Basis

(* Type Checking *)
(* Author: Carsten Schuermann *)
module type TYPECHECK = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string

  val check : IntSyn.exp_ * IntSyn.exp_ -> unit
  val checkDec : IntSyn.dctx * (IntSyn.dec_ * IntSyn.sub_) -> unit
  val checkConv : IntSyn.exp_ * IntSyn.exp_ -> unit
  val infer : IntSyn.exp_ -> IntSyn.exp_
  val infer' : IntSyn.dctx * IntSyn.exp_ -> IntSyn.exp_
  val typeCheck : IntSyn.dctx * (IntSyn.exp_ * IntSyn.exp_) -> unit
  val typeCheckCtx : IntSyn.dctx -> unit

  (* val typeCheckSpine : IntSyn.dctx * IntSyn.Spine -> unit *)
  val typeCheckSub : IntSyn.dctx * IntSyn.sub_ * IntSyn.dctx -> unit
end
(* signature TYPECHECK *)
