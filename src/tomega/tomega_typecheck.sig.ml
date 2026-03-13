open! Basis
module Tomega = Lambda_.Tomega

(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao *)
module type TOMEGATYPECHECK = sig
  exception Error of string

  val checkCtx : Tomega.dec_ IntSyn.ctx_ -> unit
  val checkFor : Tomega.dec_ IntSyn.ctx_ * Tomega.for_ -> unit
  val checkPrg : Tomega.dec_ IntSyn.ctx_ * (Tomega.prg_ * Tomega.for_) -> unit

  val checkSub :
    Tomega.dec_ IntSyn.ctx_ * Tomega.sub_ * Tomega.dec_ IntSyn.ctx_ -> unit
end
(* Signature TOMEGATYPECHECK *)
