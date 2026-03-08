open! Basis

(* Worldify *)
(* Author: Carsten Schuermann *)
module type WORLDIFY = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Error of string

  val worldify : IntSyn.cid -> IntSyn.conDec_ list
  val worldifyGoal : IntSyn.dec_ IntSyn.ctx_ * IntSyn.exp_ -> IntSyn.exp_
end
(*  val check : Tomega.Worlds -> IntSyn.cid list -> unit
  val closure : Tomega.Worlds -> Tomega.Worlds *)
(* signature WORLDIFY *)
