open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Table
open! Table.Table_
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
open! Solvers
open! Solvers.Solvers_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Timing
open! Timing.Timing_

(* # 1 "src/unique/Unique_.sig.ml" *)
open! Basis

(* Uniqueness Checking *)

(** Author: Frank Pfenning *)

module type UNIQUE = sig
  exception Error of string

  val checkUnique : IntSyn.cid * Modesyn.ModeSyn.modeSpine -> unit
end
