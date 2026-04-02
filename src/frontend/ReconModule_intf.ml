(* # 1 "src/frontend/ReconModule.sig.ml" *)
open! Basis

(* External syntax for module expressions *)
(* Author: Kevin Watkins *)

module type MODEXTSYN = sig
  module ExtSyn : ReconTerm_intf.EXTSYN

  (*! structure Paths : PATHS !*)
  type strexp

  val strexp : string list * string * Paths.region -> strexp

  type inst

  val coninst :
    (string list * string * Paths.region) * ExtSyn.term * Paths.region -> inst

  val strinst :
    (string list * string * Paths.region) * strexp * Paths.region -> inst

  type sigexp

  val thesig : sigexp
  val sigid : string * Paths.region -> sigexp
  val wheresig : sigexp * inst list -> sigexp

  type sigdef

  val sigdef : string option * sigexp -> sigdef

  type structdec

  val structdec : string option * sigexp -> structdec
  val structdef : string option * strexp -> structdec
end

module type RECON_MODULE = sig
  include MODEXTSYN
  module ModSyn : Modsyn.MODSYN

  exception Error of string

  type whereclause

  type structDec =
    | StructDec of string option * ModSyn.module_ * whereclause list
    | StructDef of string option * IntSyn.mid

  val strexpToStrexp : strexp -> IntSyn.mid

  val sigexpToSigexp :
    sigexp * ModSyn.module_ option -> ModSyn.module_ * whereclause list

  val sigdefToSigdef :
    sigdef * ModSyn.module_ option ->
    string option * ModSyn.module_ * whereclause list

  val structdecToStructDec : structdec * ModSyn.module_ option -> structDec
  val moduleWhere : ModSyn.module_ * whereclause -> ModSyn.module_
end
