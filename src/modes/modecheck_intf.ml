(* # 1 "src/modes/modecheck.sig.ml" *)
open! Basis
open Modesyn

(* Mode Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

module type MODECHECK = sig
  exception Error of string

  (* for new declarations *)
  val checkD : IntSyn.conDec * string * Paths.occConDec option -> unit

  (* raises Error (msg) *)
  (* for prior declarations *)
  val checkMode : IntSyn.cid * ModeSyn.modeSpine -> unit

  (* raises Error(msg) *)
  (* for output coverage of prior declarations *)
  val checkFreeOut : IntSyn.cid * ModeSyn.modeSpine -> unit
end
