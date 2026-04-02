(* # 1 "src/meta/Funtypecheck.sig.ml" *)
open! Basis
open Funprint
open Funsyn
open Statesyn

(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)

module type FUNTYPECHECK = sig
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  val isFor : IntSyn.dctx * FunSyn.for_ -> unit
  val check : FunSyn.pro * FunSyn.for_ -> unit
  val checkSub : FunSyn.lfctx * IntSyn.sub * FunSyn.lfctx -> unit
  val isState : StateSyn.state -> unit
end
