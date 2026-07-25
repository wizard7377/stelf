(* # 1 "src/global/Global_.sig.ml" *)

open Basis

(* Global parameters *)

(** Author: Frank Pfenning *)

module type GLOBAL = sig
  val chatter : int ref
  val style : int ref
  val maxCid : int
  val maxMid : int
  val maxCSid : int
  val doubleCheck : bool ref
  val unsafe : bool ref
  val autoFreeze : bool ref
  val timeLimit : Time.time option ref
  val arrow_reserved : bool ref
  val arrow_infix : bool ref
  val latin_uppercase : bool ref
  val bar_in_block : bool ref
  val old_some : bool ref
  val stop_reserved : bool ref
  val printArrowSugar : bool ref
end
