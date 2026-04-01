(* # 1 "src/order/order.sig.ml" *)
open! Basis

(* Termination Order *)

(** Author: Carsten Schuermann *)

module type ORDER = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string

  type 'a order = Arg of 'a | Lex of 'a order list | Simul of 'a order list
  [@@deriving eq, ord, show]

  (* Orders                     *)
  (* O ::= x                    *)
  (*     | {O1 .. On}           *)

  (** | [O1 .. On] *)
  type predicate =
    | Less of int order * int order
    | Leq of int order * int order
    | Eq of int order * int order
  [@@deriving eq, ord, show]

  (* Reduction Order            *)
  (* O < O'                     *)
  (* O <= O'                    *)

  (** O = O' *)
  type mutual = Empty | Le of IntSyn.cid * mutual | Lt of IntSyn.cid * mutual
  [@@deriving eq, ord, show]

  (* Termination ordering       *)
  (* O ::= No order specified   *)
  (*     | mutual dependencies  *)

  (** | lex order for - *)
  type tDec = TDec of int order * mutual [@@deriving eq, ord, show]

  (** Termination declaration *)
  type rDec = RDec of predicate * mutual [@@deriving eq, ord, show]

  val reset : unit -> unit
  (** Reduction declaration *)

  val resetROrder : unit -> unit
  val install : IntSyn.cid * tDec -> unit
  val uninstall : IntSyn.cid -> bool
  val installROrder : IntSyn.cid * rDec -> unit
  val uninstallROrder : IntSyn.cid -> bool
  val selLookup : IntSyn.cid -> int order
  val selLookupROrder : IntSyn.cid -> predicate
  val mutLookup : IntSyn.cid -> mutual
  val closure : IntSyn.cid -> IntSyn.cid list
end
