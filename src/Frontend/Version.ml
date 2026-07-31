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

(* # 1 "src/frontend/Version.sig.ml" *)

(* # 1 "src/frontend/Version.fun.ml" *)

(* # 1 "src/frontend/Version.sml.ml" *)
open! Basis

module Version = struct
  let current_version = "1.7.1"
  let current_version_revision = "1813"
  let build_revision = "exported"
  let build_date = "unknown-date"
  let build_hostname = "unknown-host"

  let maybe arg__0 arg__1 =
    begin match (arg__0, arg__1) with true, x -> x | false, x -> ""
    end

  let official = build_revision = current_version_revision
  let external_ = build_revision = "exported"

  let version_string =
    (((((((("Stelf " ^ current_version) ^ maybe (not official) "+") ^ " (")
        ^ maybe ((not external_) && not official) (("r" ^ build_revision) ^ ", ")
        )
       ^ "built ")
      ^ build_date)
     ^ " on ")
    ^ build_hostname)
    ^ ")"
end
