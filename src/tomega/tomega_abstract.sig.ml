open! Basis
module Tomega = Lambda_.Tomega

(* Abstraction mechanisms form programs and formulas *)
(* Author: Carsten Schuermann *)
module type TOMEGAABSTRACT = sig
  exception Error of string

  val raiseFor :
    IntSyn.dec_ IntSyn.ctx_ * (Tomega.for_ * IntSyn.sub_) -> Tomega.for_

  val raisePrg :
    IntSyn.dec_ IntSyn.ctx_ * Tomega.prg_ * Tomega.for_ -> Tomega.prg_

  val raiseP :
    IntSyn.dec_ IntSyn.ctx_ * Tomega.prg_ * Tomega.for_ -> Tomega.prg_

  val raiseF :
    IntSyn.dec_ IntSyn.ctx_ * (Tomega.for_ * IntSyn.sub_) -> Tomega.for_
end
(* Signature TOMEGAABSTRACT *)
