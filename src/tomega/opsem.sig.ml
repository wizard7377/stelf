open! Basis

(* Operational Semantics for Delphin *)
(* Author: Carsten Schuermann *)
module type OPSEM = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception NoMatch

  val evalPrg : Tomega.prg_ -> Tomega.prg_
  val topLevel : Tomega.prg_ -> unit

  val createVarSub :
    Tomega.dec_ IntSyn.ctx_ * Tomega.dec_ IntSyn.ctx_ -> Tomega.sub_

  val matchSub : Tomega.dec_ IntSyn.ctx_ * Tomega.sub_ * Tomega.sub_ -> unit
end
