open! Basis
open Compsyn

(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Frank Pfenning *)
module type COMPILE = sig
  (*! structure IntSyn: INTSYN !*)
  (*! structure CompSyn: COMPSYN !*)
  exception Error of string

  type opt_ = CompSyn.opt_

  val optimize : opt_ ref
  val install : IntSyn.conDecForm_ -> IntSyn.cid -> unit
  val sProgReset : unit -> unit
  val compileCtx : bool -> IntSyn.dec_ IntSyn.ctx_ -> CompSyn.dProg_
  val compileGoal : IntSyn.dec_ IntSyn.ctx_ * IntSyn.exp_ -> CompSyn.goal_

  (* for the meta theorem prover  --cs *)
  val compilePsi : bool -> Tomega.dec_ IntSyn.ctx_ -> CompSyn.dProg_
end
(* signature COMPILE *)
