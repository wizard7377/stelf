open! Basis

(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)
module type CPRINT = sig
  open CompSyn

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  val goalToString : string -> IntSyn.dctx * CompSyn.goal_ -> string
  val clauseToString : string -> IntSyn.dctx * CompSyn.resGoal_ -> string
  val sProgToString : unit -> string
  val dProgToString : CompSyn.dProg_ -> string
  val subgoalsToString : string -> IntSyn.dctx * CompSyn.conjunction_ -> string
end
(* signature CPRINT *)
