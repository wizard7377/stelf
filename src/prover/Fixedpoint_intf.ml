(* # 1 "src/prover/Fixedpoint.sig.ml" *)
open! Basis

(* Splitting: Version 1.4 *)
(* Author: Carsten Schuermann *)

module type FIXEDPOINT = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  module State : State.STATE

  exception Error of string

  type operator

  val expand : State.focus * Tomega.tC -> operator
  val apply : operator -> unit
  val menu : operator -> string
end
