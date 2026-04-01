(* # 1 "src/names/names_.sig.ml" *)
open! Basis

(* Names of Constants and Variables *)
(* Author: Frank Pfenning *)

(** Modified: Jeff Polakow *)

module type FIXITY = sig
  type associativity = Left | Right | None [@@deriving eq, ord, show]
  type precedence = Strength of int [@@deriving eq, ord, show]

  val maxPrec : precedence
  val minPrec : precedence
  val less : precedence * precedence -> bool
  val leq : precedence * precedence -> bool
  val compare : precedence * precedence -> order
  val inc : precedence -> precedence
  val dec : precedence -> precedence

  type fixity =
    | Nonfix
    | Infix of precedence * associativity
    | Prefix of precedence
    | Postfix of precedence
  [@@deriving eq, ord, show]

  val prec : fixity -> precedence
  val toString : fixity -> string

  val precToIntAsc : fixity -> int
  (** returns integer for precedence such that lower values correspond to higher
      precedence, useful for exports *)
end

module type NAMES = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string
  exception Unprintable

  module Fixity : FIXITY

  (** Constant names and fixities *)
  type qid = Qid of string list * string [@@deriving eq, ord, show]

  val qidToString : qid -> string
  val stringToQid : string -> qid option
  val unqualified : qid -> string option

  type namespace

  val newNamespace : unit -> namespace
  val insertConst : namespace * IntSyn.cid -> unit

  val insertStruct : namespace * IntSyn.mid -> unit
  (** shadowing disallowed *)

  val appConsts : (string * IntSyn.cid -> unit) -> namespace -> unit
  (** shadowing disallowed *)

  val appStructs : (string * IntSyn.mid -> unit) -> namespace -> unit
  val reset : unit -> unit
  val resetFrom : IntSyn.cid * IntSyn.mid -> unit

  val installConstName : IntSyn.cid -> unit
  (** The following functions have to do with the mapping from names to
      cids/mids only. *)

  val installStructName : IntSyn.mid -> unit
  val constLookup : qid -> IntSyn.cid option
  val structLookup : qid -> IntSyn.mid option
  val constUndef : qid -> qid option

  val structUndef : qid -> qid option
  (** shortest undefined prefix of Qid *)

  val constLookupIn : namespace * qid -> IntSyn.cid option
  val structLookupIn : namespace * qid -> IntSyn.mid option
  val constUndefIn : namespace * qid -> qid option
  val structUndefIn : namespace * qid -> qid option

  val conDecQid : IntSyn.conDec -> qid
  (** This function maps cids/mids to names. It uses the information in the
      IntSyn.ConDec or IntSyn.StrDec entries only, and only considers the
      name->cid/mid mapping defined above in order to tell whether a name is
      shadowed (any constant or structure whose canonical name would map to
      something else, or to nothing at all, in the case of an anonymous
      structure, is shadowed). *)

  val constQid : IntSyn.cid -> qid

  val structQid : IntSyn.mid -> qid
  (** will mark if shadowed *)

  val installFixity : IntSyn.cid * Fixity.fixity -> unit
  (** will mark if shadowed *)

  val getFixity : IntSyn.cid -> Fixity.fixity
  val fixityLookup : qid -> Fixity.fixity

  (* Nonfix if undefined *)

  val installNamePref : IntSyn.cid * (string list * string list) -> unit
  (** Name preferences for anonymous variables: a, EPref, UPref *)

  val getNamePref : IntSyn.cid -> (string list * string list) option
  val installComponents : IntSyn.mid * namespace -> unit
  val getComponents : IntSyn.mid -> namespace

  val varReset : IntSyn.dctx -> unit
  (** EVar and BVar name choices *)

  val addEVar : IntSyn.exp * string -> unit
  (** context in which EVars are created *)

  val getEVarOpt : string -> IntSyn.exp option
  (** assumes name not already used *)

  val evarName : IntSyn.dctx * IntSyn.exp -> string
  (** NONE, if undefined or not EVar *)

  val bvarName : IntSyn.dctx * int -> string
  (** create, if undefined *)

  val decName : IntSyn.dctx * IntSyn.dec -> IntSyn.dec
  (** raises Unprintable if undefined *)

  val decEName : IntSyn.dctx * IntSyn.dec -> IntSyn.dec
  (** status unknown, like decEName *)

  val decUName : IntSyn.dctx * IntSyn.dec -> IntSyn.dec
  (** assign existential name *)

  val decLUName : IntSyn.dctx * IntSyn.dec -> IntSyn.dec
  (** assign universal name *)

  val ctxName : IntSyn.dctx -> IntSyn.dctx
  (** assign local universal name *)

  val ctxLUName : IntSyn.dctx -> IntSyn.dctx
  (** assign global existential names *)

  val nameConDec : IntSyn.conDec -> IntSyn.conDec
  (** assign local universal names *)

  val skonstName : string -> string
  (** Skolem constants *)

  val namedEVars : unit -> (IntSyn.exp * string) list
  (** Named EVars, used for queries *)

  val evarCnstr : unit -> (IntSyn.exp * string) list
  (** Uninstantiated named EVars with constraints *)
end
