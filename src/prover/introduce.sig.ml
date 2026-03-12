open! Basis

(* Introduce: Version 1.4 *)
(* Author: Carsten Schuermann *)
module type INTRODUCE = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  module State : State.STATE

  exception Error of string

  type nonrec operator

  val expand : State.focus_ -> operator option
  val apply : operator -> unit
  val menu : operator -> string
end
(* signature INTRODUCE *)
