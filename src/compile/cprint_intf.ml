(* # 1 "src/compile/cprint.sig.ml" *)
open! Basis

(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)

module type CPRINT = sig
  open CompSyn

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  val goalToString : string -> IntSyn.dctx * CompSyn.goal -> string
  val clauseToString : string -> IntSyn.dctx * CompSyn.resGoal -> string
  val sProgToString : unit -> string
  val dProgToString : CompSyn.dProg -> string
  val subgoalsToString : string -> IntSyn.dctx * CompSyn.conjunction -> string
end
