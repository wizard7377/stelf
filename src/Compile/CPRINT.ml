open! Basis
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Formatter
open! Formatter__Formatter_
open! Index
open! Index.Index_
open! Typecheck
open! Typecheck.Typecheck_
open! Solvers
open! Solvers.Solvers_
open! Subordinate
open! Subordinate

(* # 1 "src/compile/Cprint.sig.ml" *)
open! Basis

(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)

module type CPRINT = sig
  open CompSyn

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  val goalToString : string -> IntSyn.dctx * CompSyn.goal -> string
  val clauseToString : string -> IntSyn.dctx * CompSyn.resGoal -> string
  val sProgToString : unit -> string
  val dProgToString : CompSyn.dProg -> string
  val subgoalsToString : string -> IntSyn.dctx * CompSyn.conjunction -> string
end
