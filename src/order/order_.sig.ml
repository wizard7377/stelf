open! Basis

(* Termination Order *)
(* Author: Carsten Schuermann *)
module type ORDER = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string

  type 'a order_ = Arg of 'a | Lex of 'a order_ list | Simul of 'a order_ list

  (* Orders                     *)
  (* O ::= x                    *)
  (*     | {O1 .. On}           *)
  (*     | [O1 .. On]           *)
  type predicate_ =
    | Less of int order_ * int order_
    | Leq of int order_ * int order_
    | Eq of int order_ * int order_

  (* Reduction Order            *)
  (* O < O'                     *)
  (* O <= O'                    *)
  (* O = O'                     *)
  type mutual_ =
    | Empty
    | Le of IntSyn.cid * mutual_
    | Lt of IntSyn.cid * mutual_

  (* Termination ordering       *)
  (* O ::= No order specified   *)
  (*     | mutual dependencies  *)
  (*     | lex order for  -     *)
  type tDec_ = TDec of int order_ * mutual_

  (* Termination declaration *)
  type rDec_ = RDec of predicate_ * mutual_

  (* Reduction declaration      *)
  val reset : unit -> unit
  val resetROrder : unit -> unit
  val install : IntSyn.cid * tDec_ -> unit
  val uninstall : IntSyn.cid -> bool
  val installROrder : IntSyn.cid * rDec_ -> unit
  val uninstallROrder : IntSyn.cid -> bool
  val selLookup : IntSyn.cid -> int order_
  val selLookupROrder : IntSyn.cid -> predicate_
  val mutLookup : IntSyn.cid -> mutual_
  val closure : IntSyn.cid -> IntSyn.cid list
end
(* signature ORDER *)
