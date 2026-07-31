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

(* # 1 "src/m2/M2_.sig.ml" *)

(* # 1 "src/m2/M2_.fun.ml" *)

(* # 1 "src/m2/M2_.sml.ml" *)
open! Basis
open MetaPrint
open Init
open Search
open Lemma
open Splitting
open Filling
open Recursion
open Qed
open Strategy
open Prover
open Mpi
open Skolem
module Skolem : SKOLEM.SKOLEM
module IndexSkolem : INDEX.INDEX
module M2Prover : PROVER.PROVER
