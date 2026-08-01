open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Formatter
open! Formatter__Formatter_

(* # 1 "src/print/ClausePrint.sig.ml" *)
open! Basis

(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)

module type CLAUSEPRINT = sig
  (*! structure IntSyn : INTSYN !*)
  module Formatter : FORMATTER

  val formatClause : IntSyn.dctx -> IntSyn.exp -> Formatter.format
  val formatConDec : IntSyn.conDec -> Formatter.format
  val clauseToString : IntSyn.dctx -> IntSyn.exp -> string
  val conDecToString : IntSyn.conDec -> string
  val printSgn : unit -> unit
end
