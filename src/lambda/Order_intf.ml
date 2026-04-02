(* # 1 "src/lambda/Order.sig.ml" *)
open! Basis
(** Termination and reduction order declarations for LF constants. *)

open Intsyn

(* Termination Order *)
(* Author: Carsten Schuermann *)

module type ORDER = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string

  type 'a order = Arg of 'a | Lex of 'a order list | Simul of 'a order list
  [@@deriving eq, ord, show]

  (* Orders                     *)
  (* O ::= x                    *)
  (*     | {O1 .. On}           *)
  (*     | [O1 .. On]           *)
  type predicate =
    | Less of int order * int order
    | Leq of int order * int order
    | Eq of int order * int order
  [@@deriving eq, ord, show]

  (* Reduction Order            *)
  (* O < O'                     *)
  (* O <= O'                    *)
  (* O = O'                     *)
  type mutual = Empty | Le of IntSyn.cid * mutual | Lt of IntSyn.cid * mutual
  [@@deriving eq, ord, show]

  (* Termination ordering       *)
  (* O ::= No order specified   *)
  (*     | mutual dependencies  *)
  (*     | lex order for  -     *)
  type tDec = TDec of int order * mutual [@@deriving eq, ord, show]

  (* Termination declaration *)
  type rDec = RDec of predicate * mutual [@@deriving eq, ord, show]

  (* Reduction declaration      *)
  val reset : unit -> unit
  val reset_r_order : unit -> unit

  val resetROrder : unit -> unit
  (** Compatibility alias for {!reset_r_order}. *)

  val install : IntSyn.cid * tDec -> unit
  val uninstall : IntSyn.cid -> bool
  val install_r_order : IntSyn.cid * rDec -> unit

  val installROrder : IntSyn.cid * rDec -> unit
  (** Compatibility alias for {!install_r_order}. *)

  val uninstall_r_order : IntSyn.cid -> bool

  val uninstallROrder : IntSyn.cid -> bool
  (** Compatibility alias for {!uninstall_r_order}. *)

  val sel_lookup : IntSyn.cid -> int order

  val selLookup : IntSyn.cid -> int order
  (** Compatibility alias for {!sel_lookup}. *)

  val sel_lookup_r_order : IntSyn.cid -> predicate

  val selLookupROrder : IntSyn.cid -> predicate
  (** Compatibility alias for {!sel_lookup_r_order}. *)

  val mut_lookup : IntSyn.cid -> mutual

  val mutLookup : IntSyn.cid -> mutual
  (** Compatibility alias for {!mut_lookup}. *)

  val closure : IntSyn.cid -> IntSyn.cid list
end
