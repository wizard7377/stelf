(* # 1 "src/tomega/TomegaAbstract.sig.ml" *)
open! Basis

module type TOMEGAABSTRACT = sig
  exception Error of string

  val raiseFor :
    IntSyn.dec IntSyn.ctx * (Tomega.for_ * IntSyn.sub) -> Tomega.for_

  val raisePrg : IntSyn.dec IntSyn.ctx * Tomega.prg * Tomega.for_ -> Tomega.prg
  val raiseP : IntSyn.dec IntSyn.ctx * Tomega.prg * Tomega.for_ -> Tomega.prg
  val raiseF : IntSyn.dec IntSyn.ctx * (Tomega.for_ * IntSyn.sub) -> Tomega.for_
end
