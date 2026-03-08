open! Basis
open Intsyn

(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)
module type UNIFY = sig
  (*! structure IntSyn : INTSYN !*)
  type nonrec unifTrail

  (* suspending and resuming trailing *)
  val suspend : unit -> unifTrail
  val resume : unifTrail -> unit

  (* trailing of variable instantiation *)
  val reset : unit -> unit
  val mark : unit -> unit
  val unwind : unit -> unit

  val instantiateEVar :
    IntSyn.exp_ option ref * IntSyn.exp_ * IntSyn.cnstr list -> unit

  val instantiateLVar : IntSyn.block_ option ref * IntSyn.block_ -> unit
  val resetAwakenCnstrs : unit -> unit
  val nextCnstr : unit -> IntSyn.cnstr option
  val addConstraint : IntSyn.cnstr list ref * IntSyn.cnstr -> unit
  val solveConstraint : IntSyn.cnstr -> unit
  val delay : IntSyn.eclo * IntSyn.cnstr -> unit

  (* unification *)
  val intersection : IntSyn.sub_ * IntSyn.sub_ -> IntSyn.sub_

  exception Unify of string

  val unify : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit

  (* raises Unify *)
  val unifyW : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit

  (* raises Unify *)
  val unifyBlock : IntSyn.dctx * IntSyn.block_ * IntSyn.block_ -> unit

  (* raises Unify *)
  val unifySub : IntSyn.dctx * IntSyn.sub_ * IntSyn.sub_ -> unit

  (* raises Unify *)
  val invertible :
    IntSyn.dctx * IntSyn.eclo * IntSyn.sub_ * IntSyn.exp_ option ref -> bool

  val invertSub :
    IntSyn.dctx * IntSyn.sub_ * IntSyn.sub_ * IntSyn.exp_ option ref ->
    IntSyn.sub_

  (* unifiable (G, Us,Us') will instantiate EVars as an effect *)
  val unifiable : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool

  (* unifiable' (G, Us,Us') is like unifiable, but returns NONE for
     success and SOME(msg) for failure *)
  val unifiable' : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> string option
end
(* signature UNIFY *)
