open! Intsyn.Lambda_

(* # 1 "src/names/Names_.sig.ml" *)
open! Basis

(* Names of Constants and Variables *)
(* Author: Frank Pfenning *)

(** Modified: Jeff Polakow *)

module type FIXITY = sig
  type associativity = Left | Right | None [@@deriving eq, ord, show]
  type precedence = Strength of int [@@deriving eq, ord, show]

  val maxPrec : precedence
  val minPrec : precedence
  val less : precedence -> precedence -> bool
  val leq : precedence -> precedence -> bool
  val compare : precedence -> precedence -> order
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
  val insertConst : namespace -> IntSyn.cid -> unit

  val insertConstShadow : namespace -> IntSyn.cid -> unit
  (** Like [insertConst], but silently replaces an existing same-named member
      instead of raising [Error]. Used by [%scope] reopening, where a judgment's
      later case clause is allowed to reuse an earlier clause's label (the
      earlier constant keeps its own [cid] and stays in the signature; it just
      stops being reachable by that name). *)

  val insertStruct : namespace -> IntSyn.mid -> unit
  (** shadowing disallowed *)

  val appConsts : (string * IntSyn.cid -> unit) -> namespace -> unit
  (** shadowing disallowed *)

  val appStructs : (string * IntSyn.mid -> unit) -> namespace -> unit
  val reset : unit -> unit
  val resetFrom : IntSyn.cid -> IntSyn.mid -> unit

  val installConstName : IntSyn.cid -> unit
  (** The following functions have to do with the mapping from names to
      cids/mids only. *)

  val uninstallConst : IntSyn.cid -> unit
  (** Undo a single [installConstName cid], restoring whatever it shadowed (or
      removing it from the global table if it shadowed nothing). Used to retract
      a %scope body's global bindings once the scope closes, without touching
      signature/structure bookkeeping the way [resetFrom] does. *)

  val installStructName : IntSyn.mid -> unit
  val constLookup : qid -> IntSyn.cid option
  val structLookup : qid -> IntSyn.mid option
  val constUndef : qid -> qid option

  val currentGroupNamespace : namespace ref
  (** The namespace of the %require group currently being loaded (or the
      top-level namespace if none). [Pal.Impl]'s [current_group_ns] is an alias
      for this ref -- see [resolveQid] for why this needs to live here rather
      than in [Impl.ml]. *)

  val resolveQid : shortest:bool -> qid -> IntSyn.cid option
  (** Shared entry point for %val/%abs name resolution. [shortest:false] (%val)
      is shadow-aware lookup, identical to [constLookup]. [shortest:true] (%abs)
      on an unqualified [qid] prefers a toplevel declaration within
      [!currentGroupNamespace], falling back to shadow-aware lookup if none
      exists; on a qualified [qid] it is identical to [constLookup]. *)

  val structUndef : qid -> qid option
  (** shortest undefined prefix of Qid *)

  val constLookupIn : namespace -> qid -> IntSyn.cid option
  val structLookupIn : namespace -> qid -> IntSyn.mid option
  val constUndefIn : namespace -> qid -> qid option
  val structUndefIn : namespace -> qid -> qid option

  val conDecQid : IntSyn.conDec -> qid
  (** This function maps cids/mids to Names. It uses the information in the
      IntSyn.ConDec or IntSyn.StrDec entries only, and only considers the
      name->cid/mid mapping defined above in order to tell whether a name is
      shadowed (any constant or structure whose canonical name would map to
      something else, or to nothing at all, in the case of an anonymous
      structure, is shadowed). *)

  val constQid : IntSyn.cid -> qid

  val constPath : IntSyn.cid -> qid option
  (** [constPath cid] is a qualified name that reaches [cid] through the
      structure it was declared in, or [None] if there is none. Unlike
      [constQid] it never returns a marker: either the qid resolves back to
      [cid] or the answer is [None]. Use it to recover a printable name for a
      constant [constQid] has marked as shadowed. *)

  val structQid : IntSyn.mid -> qid
  (** will mark if shadowed *)

  val installFixity : IntSyn.cid -> Fixity.fixity -> unit
  (** will mark if shadowed *)

  val getFixity : IntSyn.cid -> Fixity.fixity
  val fixityLookup : qid -> Fixity.fixity

  (* Nonfix if undefined *)

  val installAlias : string -> IntSyn.cid -> unit
  (** [installAlias (name, cid)] registers [name] as an additional lookup name
      for constant [cid] in the global namespace. *)

  val insertConstAlias : namespace -> string -> IntSyn.cid -> unit
  (** [insertConstAlias (ns, name, cid)] registers [name] as an additional
      lookup name for constant [cid] in the given namespace [ns]. *)

  val installNamePref : IntSyn.cid -> string list * string list -> unit
  (** Name preferences for anonymous variables: a, EPref, UPref *)

  val getNamePref : IntSyn.cid -> (string list * string list) option
  val installComponents : IntSyn.mid -> namespace -> unit
  val getComponents : IntSyn.mid -> namespace

  val varReset : IntSyn.dctx -> unit
  (** EVar and BVar name choices *)

  val addEVar : IntSyn.exp -> string -> unit
  (** context in which EVars are created *)

  val getEVarOpt : string -> IntSyn.exp option
  (** assumes name not already used *)

  val evarName : IntSyn.dctx -> IntSyn.exp -> string
  (** NONE, if undefined or not EVar *)

  val bvarName : IntSyn.dctx -> int -> string
  (** create, if undefined *)

  val decName : IntSyn.dctx -> IntSyn.dec -> IntSyn.dec
  (** raises Unprintable if undefined *)

  val decEName : IntSyn.dctx -> IntSyn.dec -> IntSyn.dec
  (** status unknown, like decEName *)

  val decUName : IntSyn.dctx -> IntSyn.dec -> IntSyn.dec
  (** assign existential name *)

  val decLUName : IntSyn.dctx -> IntSyn.dec -> IntSyn.dec
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

module type WRAP = sig 
    module Fixity : FIXITY
    module type S = NAMES with module Fixity = Fixity
    type t
    val wrap : (module S) -> t
    val unwrap : t -> (module S)
end