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

(* # 1 "src/m2/MetaGlobal.sig.ml" *)
open! Basis

(* Global parameters *)
(* Author: Carsten Schuermann *)
include METAGLOBAL
(* signature METAGLOBAL *)

(* # 1 "src/m2/MetaGlobal.fun.ml" *)

(* # 1 "src/m2/MetaGlobal.sml.ml" *)
open! Basis

(* Global parameters *)
(* Author: Carsten Schuermann *)
module MetaGlobal : METAGLOBAL = struct
  type strategy = Rfs | Frs [@@deriving eq, ord, show]

  let strategy = ref Frs
  let maxFill = ref 6
  let maxSplit = ref 2
  let maxRecurse = ref 10
end
(* structure MetaGlobal *)
