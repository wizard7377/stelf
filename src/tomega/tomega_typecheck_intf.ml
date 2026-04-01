(* # 1 "src/tomega/tomega_typecheck.sig.ml" *)
open! Basis

module type TOMEGATYPECHECK = sig
  exception Error of string

  val checkCtx : Tomega.dec IntSyn.ctx -> unit
  val checkFor : Tomega.dec IntSyn.ctx * Tomega.for_ -> unit
  val checkPrg : Tomega.dec IntSyn.ctx * (Tomega.prg * Tomega.for_) -> unit

  val checkSub :
    Tomega.dec IntSyn.ctx * Tomega.sub * Tomega.dec IntSyn.ctx -> unit
end
