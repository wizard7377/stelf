(* # 1 "src/subordinate/Subordinate_.sig.ml" *)
open! Basis

(* Subordination *)
(* Author: Carsten Schuermann *)

(** Modified: Frank Pfenning *)

module type SUBORDINATE = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string

  val reset : unit -> unit
  val install : IntSyn.cid -> unit
  val installDef : IntSyn.cid -> unit
  val installBlock : IntSyn.cid -> unit

  (* val installFrozen : IntSyn.cid list -> unit *)

  val freeze : IntSyn.cid list -> IntSyn.cid list
  (** superseded by freeze *)

  val thaw : IntSyn.cid list -> IntSyn.cid list
  (** transitive freeze, returns frozen cids *)

  val frozen : IntSyn.cid list -> bool
  (** reverse transitive thaw, returns thawed cids *)

  val addSubord : IntSyn.cid * IntSyn.cid -> unit
  (** any cid in list frozen? *)

  val below : IntSyn.cid * IntSyn.cid -> bool

  val belowEq : IntSyn.cid * IntSyn.cid -> bool
  (** transitive closure *)

  val equiv : IntSyn.cid * IntSyn.cid -> bool
  (** refl. transitive closure *)

  val respects : IntSyn.dctx * IntSyn.eclo -> unit
  (** mutual dependency *)

  val respectsN : IntSyn.dctx * IntSyn.exp -> unit
  (** respects current subordination? *)

  val checkNoDef : IntSyn.cid -> unit
  (** respectsN(G, V), V in nf *)

  val weaken : IntSyn.dctx * IntSyn.cid -> IntSyn.sub
  (** not involved in type-level definition? *)

  val show : unit -> unit
  val showDef : unit -> unit
end
