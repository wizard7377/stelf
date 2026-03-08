open! Basis
open Modesyn

(* Modes: short and long forms *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
module type MODEDEC = sig
  exception Error of string

  val shortToFull :
    IntSyn.cid * ModeSyn.modeSpine_ * Paths.region -> ModeSyn.modeSpine_

  val checkFull : IntSyn.cid * ModeSyn.modeSpine_ * Paths.region -> unit
  val checkPure : (IntSyn.cid * ModeSyn.modeSpine_) * Paths.region -> unit
end
(* signature MODEDEC *)
