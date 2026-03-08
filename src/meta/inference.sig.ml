open! Basis

(* Inference: Version 1.3 *)
(* Author: Carsten Schuermann *)
module type INFERENCE = sig
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  type nonrec operator

  val expand : StateSyn.state_ -> operator
  val apply : operator -> StateSyn.state_
  val menu : operator -> string
end
(* signature Inference *)
