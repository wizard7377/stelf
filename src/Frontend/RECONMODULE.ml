open! Basis
open! Timing
open! Timing.Timing_
open! Stream
open! Stream.Stream_
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Tabling
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Style
open! Style.Style_
open! Modes
open! Modes.Modes_
open! Terminate
open! Terminate.Terminate_
open! Index
open! Index.Index_
open! Thm
open! Thm.Thm_
open! M2
open! M2.M2_
open! Compile
open! Compile.Compile_
open! Opsem
open! Opsem.Opsem_
open! Subordinate
open! Subordinate
open! Modules
open! Modules.Modules_
open! Meta
open! Meta.Meta_
open! Solvers
open! Solvers.Solvers_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Unique
open! Unique.Unique_
open! Cover
open! Cover.Cover_
open! Tomega_lib
open! Tomega_lib.Tomega_
open! Prover
open! Flit
open! Flit.Flit_
open! Msg
open! Msg.Msg_

(* # 1 "src/frontend/ReconModule.sig.ml" *)
open! Basis

(* External syntax for module expressions *)
(* Author: Kevin Watkins *)

module type MODEXTSYN = sig
  module ExtSyn : RECONTERM.EXTSYN

  (*! structure Paths : PATHS !*)
  type strexp

  val strexp : string list -> string -> Paths.region -> strexp

  type inst

  val coninst :
    string list * string * Paths.region -> ExtSyn.term -> Paths.region -> inst

  val strinst :
    string list * string * Paths.region -> strexp -> Paths.region -> inst

  type sigexp

  val thesig : sigexp
  val sigid : string -> Paths.region -> sigexp
  val wheresig : sigexp -> inst list -> sigexp

  type sigdef

  val sigdef : string option -> sigexp -> sigdef

  type structdec

  val structdec : string option -> sigexp -> structdec
  val structdef : string option -> strexp -> structdec
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
    sigexp -> ModSyn.module_ option -> ModSyn.module_ * whereclause list

  val sigdefToSigdef :
    sigdef -> ModSyn.module_ option ->
    string option * ModSyn.module_ * whereclause list

  val structdecToStructDec : structdec -> ModSyn.module_ option -> structDec
  val moduleWhere : ModSyn.module_ -> whereclause -> ModSyn.module_
end
