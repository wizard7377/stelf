open! Basis

(* Weakening substitutions *)
(* Author: Carsten Schuermann *)
module type WEAKEN = sig
  (*! structure IntSyn : INTSYN !*)
  val strengthenExp : IntSyn.exp_ * IntSyn.sub_ -> IntSyn.exp_
  val strengthenSpine : IntSyn.spine_ * IntSyn.sub_ -> IntSyn.spine_
  val strengthenCtx : IntSyn.dctx * IntSyn.sub_ -> IntSyn.dctx * IntSyn.sub_
  val strengthenDec : IntSyn.dec_ * IntSyn.sub_ -> IntSyn.dec_
  val strengthenSub : IntSyn.sub_ * IntSyn.sub_ -> IntSyn.sub_
end
(* signature PRUNE *)
