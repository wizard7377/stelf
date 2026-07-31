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

(* # 1 "src/frontend/Unknownexn.sig.ml" *)
open! Basis
include UNKNOWNEXN

(* # 1 "src/frontend/Unknownexn.fun.ml" *)
open! Basis

(* Print an informative message on receipt of an unhandled exception. *)
module MakeUnknownExn (UnknownExn : sig
  val exnHistory : exn -> string list
end) : UNKNOWN_EXN = struct
  let unknownExn exn =
    let history = rev (UnknownExn.exnHistory exn) in
    let wrap1 x = ("  raised at: " ^ x) ^ "\n" in
    let wrapn x = ("             " ^ x) ^ "\n" in
    concat
      ("Unrecognized exception " :: exnName exn :: "\n"
      :: begin match history with
      | [] -> [ "" ]
      | x :: xs -> wrap1 x :: map wrapn xs
      end)
end

(* # 1 "src/frontend/Unknownexn.sml.ml" *)
