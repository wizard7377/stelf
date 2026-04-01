(* # 1 "src/worldcheck/worldSyn.sig.ml" *)
open! Basis

(* World Checking *)
(* Author: Carsten Schuermann *)

module type WORLDSYN = sig
  exception Error of string

  val reset : unit -> unit
  val install : IntSyn.cid * Tomega.worlds -> unit
  val lookup : IntSyn.cid -> Tomega.worlds

  (* raises Error if undeclared *)
  val uninstall : IntSyn.cid -> bool

  (* true if declared *)
  val worldcheck : Tomega.worlds -> IntSyn.cid -> unit
  val ctxToList : IntSyn.dec IntSyn.ctx -> IntSyn.dec list
  val isSubsumed : Tomega.worlds -> IntSyn.cid -> unit
  val getWorlds : IntSyn.cid -> Tomega.worlds
end
