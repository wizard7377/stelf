open! Basis

(* ELIM: Version 1.4 *)
(* Author: Carsten Schuermann *)
module type ELIM = sig
  module State : STATE

  exception Error of string

  type nonrec operator

  val expand : State.focus_ -> operator list
  val apply : operator -> unit
  val menu : operator -> string
end
(* signature ELIM *)
