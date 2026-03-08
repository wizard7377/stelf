open! Basis

(* Splitting: Version 1.4 *)
(* Author: Carsten Schuermann *)
module type FIXEDPOINT = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  module State : STATE

  exception Error of string

  type nonrec operator

  val expand : State.focus_ * Tomega.tC_ -> operator
  val apply : operator -> unit
  val menu : operator -> string
end
(* signature Fixed Point *)
