open! Basis
open! Global
open! Global.Global_
open! Timing
open! Timing.Timing_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Index
open! Index.Index_
open! Subordinate
open! Subordinate
open! Meta
open! Meta.Meta_
open! Solvers
open! Solvers.Solvers_

(* # 1 "src/worldcheck/Worldify.sig.ml" *)
open! Basis

(* Worldify *)
(* Author: Carsten Schuermann *)

module type WORLDIFY = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Error of string

  val worldify : IntSyn.cid -> IntSyn.conDec list
  val worldifyGoal : IntSyn.dec IntSyn.ctx * IntSyn.exp -> IntSyn.exp
end
