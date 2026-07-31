open! Basis
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Formatter
open! Formatter__Formatter_
open! Index
open! Index.Index_
open! Typecheck
open! Typecheck.Typecheck_
open! Solvers
open! Solvers.Solvers_
open! Subordinate
open! Subordinate

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
