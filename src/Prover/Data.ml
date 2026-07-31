open! Basis
open! Tomega_lib
open! Tomega_lib.Tomega_
open! Intsyn
open! Intsyn.Lambda_
open! Global
open! Global.Global_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Index
open! Index.Index_
open! Modes
open! Modes.Modes_
open! Typecheck
open! Typecheck.Typecheck_
open! Table
open! Table.Table_
open! Subordinate
open! Subordinate
open! Solvers
open! Solvers.Solvers_
open! Opsem
open! Trail
open! Trail.Trail_
open! Compile
open! Compile.Compile_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Formatter
open! Formatter__Formatter_
open! Timing
open! Timing.Timing_

(* # 1 "src/prover/Data.sig.ml" *)
open! Basis

(* Data Global parameters *)
(* Author: Carsten Schuermann *)
include DATA
(* signature DATA *)

(* # 1 "src/prover/Data.fun.ml" *)
open! Basis

(* Meta data parameters *)
(* Author: Carsten Schuermann *)
module Data : DATA = struct
  let maxFill = ref 5
  let maxSplit = ref 5
  let maxRecurse = ref 2
end
(* structure Data *)

(* # 1 "src/prover/Data.sml.ml" *)
