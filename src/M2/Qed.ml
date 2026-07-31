open! Basis
open! Stream
open! Stream.Stream_
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Modes
open! Modes.Modes_
open! Paths
open! Paths.Paths_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Terminate
open! Terminate.Terminate_
open! Index
open! Index.Index_
open! Thm
open! Thm.Thm_
open! Opsem
open! Opsem.Opsem_
open! Compile
open! Compile.Compile_
open! Subordinate
open! Subordinate
open! Table
open! Table.Table_
open! Timing
open! Timing.Timing_
open! Solvers
open! Solvers.Solvers_

(* # 1 "src/m2/Qed.sig.ml" *)
open! Basis
open Metasyn

(* Qed *)
(* Author: Carsten Schuermann *)
include QED
(* signature QED *)

(* # 1 "src/m2/Qed.fun.ml" *)
open! Basis
open Metasyn

(* QED *)
(* Author: Carsten Schuermann *)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Qed (Qed__0 : sig
  module Global : GLOBAL
  module MetaSyn' : Metasyn.METASYN
end) : QED with module MetaSyn = Qed__0.MetaSyn' = struct
  open Qed__0
  module MetaSyn = MetaSyn'

  exception Error = Error

  open! struct
    module M = MetaSyn
    module I = IntSyn

    let subgoal (M.State (name, M.Prefix (g_, m_, b_), v_)) =
      let rec check = function
        | I.Null -> true
        | I.Decl (m_, M.Top) -> check m_
        | I.Decl (m_, M.Bot) -> false
      in
      check m_
  end

  let subgoal = subgoal
end
(* local *)
(* functor Qed *)

(* # 1 "src/m2/Qed.sml.ml" *)
