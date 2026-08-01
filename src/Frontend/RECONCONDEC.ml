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

(* # 1 "src/frontend/ReconCondec.sig.ml" *)
open! Basis

(* External Syntax for signature entries *)
(* Author: Frank Pfenning *)

module type EXTCONDEC = sig
  module ExtSyn : RECONTERM.EXTSYN

  (*! structure Paths : PATHS !*)
  type condec

  (* constant declaration *)
  val condec : string * ExtSyn.term -> condec

  (* id : tm *)
  val blockdec : string -> ExtSyn.dec list -> ExtSyn.dec list -> condec
  val blockdef : string -> (string list * string) list -> condec
  val condef : string option -> ExtSyn.term -> ExtSyn.term option -> condec
end

module type RECON_CONDEC = sig
  (*! structure IntSyn : INTSYN !*)
  include EXTCONDEC

  exception Error of string

  val condecToConDec :
    condec -> Paths.location -> bool ->
    IntSyn.conDec option * Paths.occConDec option

  (* optional ConDec is absent for anonymous definitions *)
  (* bool = true means that condec is an abbreviation *)
  val internalInst :
    IntSyn.conDec -> IntSyn.conDec -> Paths.region -> IntSyn.conDec

  val externalInst : IntSyn.conDec -> ExtSyn.term -> Paths.region -> IntSyn.conDec
end
