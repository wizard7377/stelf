open! Basis

(* World Checking *)
(* Author: Carsten Schuermann *)
module type WORLDSYN = sig
  exception Error of string

  val reset : unit -> unit
  val install : IntSyn.cid * Tomega.worlds_ -> unit
  val lookup : IntSyn.cid -> Tomega.worlds_

  (* raises Error if undeclared *)
  val uninstall : IntSyn.cid -> bool

  (* true if declared *)
  val worldcheck : Tomega.worlds_ -> IntSyn.cid -> unit
  val ctxToList : IntSyn.dec_ IntSyn.ctx_ -> IntSyn.dec_ list
  val isSubsumed : Tomega.worlds_ -> IntSyn.cid -> unit
  val getWorlds : IntSyn.cid -> Tomega.worlds_
end
(* signature WORLDSYN *)
