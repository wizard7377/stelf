open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Subordinate
open! Subordinate
open! Modes
open! Modes.Modes_
open! Typecheck
open! Typecheck.Typecheck_
open! Index
open! Index.Index_
open! Opsem
open! Opsem.Opsem_
open! Compile
open! Compile.Compile_
open! Heuristic
open! Heuristic.Heuristic_
open! Timing
open! Timing.Timing_
open! Solvers
open! Solvers.Solvers_
open! M2
open! M2.M2_

(* # 1 "src/meta/Global.sig.ml" *)
open! Basis
open MetaGlobal

(* Global parameters *)
(* Author: Carsten Schuermann *)
include MTPGLOBAL
(* signature MTPGLOBAL *)

(* # 1 "src/meta/Global.fun.ml" *)
open! Basis

(* Meta Global parameters *)
(* Author: Carsten Schuermann *)
module MTPGlobal (MTPGlobal__0 : sig
  module MetaGlobal : METAGLOBAL
end) : MTPGLOBAL = struct
  type proverType = New | Old [@@deriving eq, ord, show]

  let prover = ref New
  let maxFill = MetaGlobal.maxFill
  let maxSplit = MetaGlobal.maxSplit
  let maxRecurse = MetaGlobal.maxRecurse
end
(* structure MTPGlobal *)

(* # 1 "src/meta/MtpGlobal.sml.ml" *)
