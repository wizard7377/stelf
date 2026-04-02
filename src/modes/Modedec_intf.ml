(* # 1 "src/modes/Modedec.sig.ml" *)
open! Basis
open Modesyn

(* Modes: short and long forms *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

module type MODEDEC = sig
  exception Error of string

  val shortToFull :
    IntSyn.cid * ModeSyn.modeSpine * Paths.region -> ModeSyn.modeSpine

  val checkFull : IntSyn.cid * ModeSyn.modeSpine * Paths.region -> unit
  val checkPure : (IntSyn.cid * ModeSyn.modeSpine) * Paths.region -> unit
end
