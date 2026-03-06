open! Basis;;
(* Names of Constants and Variables *);;
(* Author: Frank Pfenning *);;
(* Modified: Jeff Polakow *);;
module type FIXITY = sig
                     type associativity = | Left 
                                          | Right 
                                          | None 
                     type precedence = | Strength of int 
                     val maxPrec : precedence
                     val minPrec : precedence
                     val less : (precedence * precedence) -> bool
                     val leq : (precedence * precedence) -> bool
                     val compare : (precedence * precedence) -> order
                     val inc : precedence -> precedence
                     val dec : precedence -> precedence
                     type fixity =
                       | Nonfix 
                       | Infix of precedence * associativity 
                       | Prefix of precedence 
                       | Postfix of precedence 
                     val prec : fixity -> precedence
                     val toString : fixity -> string
                     (* returns integer for precedence such that lower values correspond to higher precedence, useful for exports *)
                     val precToIntAsc : fixity -> int
                     end;;
(* signature FIXITY *);;
module type NAMES = sig
                    (*! structure IntSyn : INTSYN !*)
                    exception Error of string 
                    exception Unprintable 
                    module Fixity : FIXITY
                    (* Constant names and fixities *)
                    type qid_ = | Qid of string list * string 
                    val qidToString : qid_ -> string
                    val stringToQid : string -> qid_ option
                    val unqualified : qid_ -> string option
                    type nonrec namespace
                    val newNamespace : unit -> namespace
                    val insertConst : (namespace * IntSyn.cid) -> unit
                    (* shadowing disallowed *)
                    val insertStruct : (namespace * IntSyn.mid) -> unit
                    (* shadowing disallowed *)
                    val
                      appConsts : ((string * IntSyn.cid) -> unit) ->
                                  namespace ->
                                  unit
                    val
                      appStructs : ((string * IntSyn.mid) -> unit) ->
                                   namespace ->
                                   unit
                    val reset : unit -> unit
                    val resetFrom : (IntSyn.cid * IntSyn.mid) -> unit
                    (* The following functions have to do with the mapping from names
     to cids/mids only. *)
                    val installConstName : IntSyn.cid -> unit
                    val installStructName : IntSyn.mid -> unit
                    val constLookup : qid_ -> IntSyn.cid option
                    val structLookup : qid_ -> IntSyn.mid option
                    val constUndef : qid_ -> qid_ option
                    (* shortest undefined prefix of Qid *)
                    val structUndef : qid_ -> qid_ option
                    val
                      constLookupIn : (namespace * qid_) -> IntSyn.cid option
                    val
                      structLookupIn : (namespace * qid_) ->
                                       IntSyn.mid
                                       option
                    val constUndefIn : (namespace * qid_) -> qid_ option
                    val structUndefIn : (namespace * qid_) -> qid_ option
                    (* This function maps cids/mids to names.  It uses the information in
     the IntSyn.ConDec or IntSyn.StrDec entries only, and only considers
     the name->cid/mid mapping defined above in order to tell whether a
     name is shadowed (any constant or structure whose canonical name
     would map to something else, or to nothing at all, in the case of
     an anonymous structure, is shadowed). *)
                    val conDecQid : IntSyn.conDec_ -> qid_
                    val constQid : IntSyn.cid -> qid_
                    (* will mark if shadowed *)
                    val structQid : IntSyn.mid -> qid_
                    (* will mark if shadowed *)
                    val installFixity : (IntSyn.cid * Fixity.fixity) -> unit
                    val getFixity : IntSyn.cid -> Fixity.fixity
                    val fixityLookup : qid_ -> Fixity.fixity
                    (* Nonfix if undefined *)
                    (* Name preferences for anonymous variables: a, EPref, UPref *)
                    val
                      installNamePref : (IntSyn.cid *
                                         (string list * string list)) ->
                                        unit
                    val
                      getNamePref : IntSyn.cid ->
                                    (string list * string list)
                                    option
                    val installComponents : (IntSyn.mid * namespace) -> unit
                    val getComponents : IntSyn.mid -> namespace
                    (* EVar and BVar name choices *)
                    val varReset : IntSyn.dctx -> unit
                    (* context in which EVars are created *)
                    val addEVar : (IntSyn.exp_ * string) -> unit
                    (* assumes name not already used *)
                    val getEVarOpt : string -> IntSyn.exp_ option
                    (* NONE, if undefined or not EVar *)
                    val evarName : (IntSyn.dctx * IntSyn.exp_) -> string
                    (* create, if undefined *)
                    val bvarName : (IntSyn.dctx * int) -> string
                    (* raises Unprintable if undefined *)
                    val decName : (IntSyn.dctx * IntSyn.dec_) -> IntSyn.dec_
                    (* status unknown, like decEName *)
                    val decEName : (IntSyn.dctx * IntSyn.dec_) -> IntSyn.dec_
                    (* assign existential name *)
                    val decUName : (IntSyn.dctx * IntSyn.dec_) -> IntSyn.dec_
                    (* assign universal name *)
                    val
                      decLUName : (IntSyn.dctx * IntSyn.dec_) -> IntSyn.dec_
                    (* assign local universal name *)
                    val ctxName : IntSyn.dctx -> IntSyn.dctx
                    (* assign global existential names *)
                    val ctxLUName : IntSyn.dctx -> IntSyn.dctx
                    (* assign local universal names *)
                    val nameConDec : IntSyn.conDec_ -> IntSyn.conDec_
                    (* Skolem constants *)
                    val skonstName : string -> string
                    (* Named EVars, used for queries *)
                    val namedEVars : unit -> (IntSyn.exp_ * string) list
                    (* Uninstantiated named EVars with constraints *)
                    val evarCnstr : unit -> (IntSyn.exp_ * string) list
                    end;;
(* signature NAMES *);;