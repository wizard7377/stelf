open! Basis
open Intsyn

(* Approximate language for term reconstruction *)
(* Author: Kevin Watkins *)
module type APPROX = sig
  (*! structure IntSyn : INTSYN !*)
  type uni_ = Level of int | Next of uni_ | LVar of uni_ option ref

  (* 1 = type, 2 = kind, 3 = hyperkind, etc. *)
  type exp_ =
    | Uni of uni_
    | Arrow of exp_ * exp_
    | Const of IntSyn.head_
    | CVar of exp_ option ref
    | Undefined

  (* Const/Def/NSDef *)
  val type_ : uni_
  val kind : uni_
  val hyperkind : uni_

  (* resets names of undetermined type/kind variables chosen for printing *)
  val varReset : unit -> unit
  val newLVar : unit -> uni_
  val newCVar : unit -> exp_
  val whnfUni : uni_ -> uni_
  val whnf : exp_ -> exp_
  val uniToApx : IntSyn.uni_ -> uni_
  val classToApx : IntSyn.exp_ -> exp_ * uni_
  val exactToApx : IntSyn.exp_ * IntSyn.exp_ -> exp_ * exp_ * uni_

  exception Ambiguous

  val apxToUni : uni_ -> IntSyn.uni_
  val apxToClass : IntSyn.dctx * exp_ * uni_ * bool -> IntSyn.exp_
  val apxToExact : IntSyn.dctx * exp_ * IntSyn.eclo * bool -> IntSyn.exp_

  exception Unify of string

  val matchUni : uni_ * uni_ -> unit
  val match_ : exp_ * exp_ -> unit
  val makeGroundUni : uni_ -> bool
end
