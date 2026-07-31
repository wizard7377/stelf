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

(* # 1 "src/frontend/ReconMode.sig.ml" *)
open! Basis

(* External Syntax of Mode Declarations *)
(* Author: Carsten Schuermann *)

module type EXTMODES = sig
  module ExtSyn : RECONTERM.EXTSYN

  (*! structure Paths : PATHS  !*)
  type mode

  val plus : Paths.region -> mode
  val star : Paths.region -> mode
  val minus : Paths.region -> mode
  val minus1 : Paths.region -> mode

  type modedec

  module Short : sig
    type mterm
    type mspine

    val mnil : Paths.region -> mspine
    val mapp : (mode * string option) * mspine -> mspine
    val mroot : string list * string * Paths.region * mspine -> mterm
    val toModedec : mterm -> modedec
  end

  module Full : sig
    type mterm

    val mroot : ExtSyn.term * Paths.region -> mterm
    val mpi : mode * ExtSyn.dec * mterm -> mterm
    val toModedec : mterm -> modedec
  end
end

module type RECON_MODE = sig
  (*! structure ModeSyn : MODESYN !*)
  include EXTMODES

  exception Error of string

  val modeToMode :
    modedec -> (IntSyn.cid * Modes.Modesyn.ModeSyn.modeSpine) * Paths.region
end
