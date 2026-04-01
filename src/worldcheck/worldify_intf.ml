(* # 1 "src/worldcheck/worldify.sig.ml" *)
open! Basis

(* Worldify *)
(* Author: Carsten Schuermann *)

module type WORLDIFY = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Error of string

  val worldify : IntSyn.cid -> IntSyn.conDec list
  val worldifyGoal : IntSyn.dec IntSyn.ctx * IntSyn.exp -> IntSyn.exp
end
