(* # 1 "src/compile/Compile_.sig.ml" *)
open! Basis
open CompSyn

(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)

(** Modified: Frank Pfenning *)

module type COMPILE = sig
  (*! structure IntSyn: INTSYN !*)
  (*! structure CompSyn: COMPSYN !*)
  exception Error of string

  type opt = CompSyn.opt

  val optimize : opt ref
  val install : IntSyn.conDecForm -> IntSyn.cid -> unit
  val sProgReset : unit -> unit
  val compileCtx : bool -> IntSyn.dec IntSyn.ctx -> CompSyn.dProg
  val compileGoal : IntSyn.dec IntSyn.ctx * IntSyn.exp -> CompSyn.goal

  val compilePsi : bool -> Tomega.dec IntSyn.ctx -> CompSyn.dProg
  (** for the meta theorem prover --cs *)
end
