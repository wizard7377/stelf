(* # 1 "src/modes/Modetable.sig.ml" *)
open! Basis
open Modesyn

(* Mode Table *)
(* Author: Frank Pfenning *)

module type MODETABLE = sig
  exception Error of string

  val reset : unit -> unit

  (* single mode installation and lookup *)
  val installMode : IntSyn.cid * ModeSyn.modeSpine -> unit
  val modeLookup : IntSyn.cid -> ModeSyn.modeSpine option
  val uninstallMode : IntSyn.cid -> bool

  (* true: was declared, false: not *)
  (* multiple mode installation and lookup *)
  val installMmode : IntSyn.cid * ModeSyn.modeSpine -> unit
  val mmodeLookup : IntSyn.cid -> ModeSyn.modeSpine list
end
