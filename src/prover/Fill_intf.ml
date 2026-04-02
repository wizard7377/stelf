(* # 1 "src/prover/Fill.sig.ml" *)
open! Basis

(* Filling: Version 1.4 *)
(* Author: Carsten Schuermann *)

module type FILL = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  module State : State.STATE

  exception Error of string

  type operator

  val expand : State.focus -> operator list
  val apply : operator -> unit
  val menu : operator -> string
end
