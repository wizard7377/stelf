(* # 1 "src/tomega/Opsem.sig.ml" *)
open! Basis

module type OPSEM = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception NoMatch

  val evalPrg : Tomega.prg -> Tomega.prg
  val topLevel : Tomega.prg -> unit
  val createVarSub : Tomega.dec IntSyn.ctx * Tomega.dec IntSyn.ctx -> Tomega.sub
  val matchSub : Tomega.dec IntSyn.ctx * Tomega.sub * Tomega.sub -> unit
end
