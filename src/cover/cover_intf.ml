(* # 1 "src/cover/cover_.sig.ml" *)
open! Basis

(* Coverage Checking *)

(** Author: Frank Pfenning *)

module type COVER = sig
  exception Error of string

  val checkNoDef : IntSyn.cid -> unit

  val checkOut : IntSyn.dctx * IntSyn.eclo -> unit
  (** raises Error(msg) *)

  val checkCovers : IntSyn.cid * Modesyn.ModeSyn.modeSpine -> unit

  val coverageCheckCases :
    Tomega.worlds * (IntSyn.dctx * IntSyn.sub) list * IntSyn.dctx -> unit
end
