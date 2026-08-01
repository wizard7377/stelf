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
open! Compile
open! Compile.Compile_
open! CompSyn
open! Assign
open! Tabling

(* # 1 "src/opsem/AbstractTabled.sig.ml" *)
open! Basis
open TableParam

(* Abstraction *)
(* Author: Brigitte Pientka *)

module type ABSTRACTTABLED = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure TableParam : TABLEPARAM !*)
  exception Error of string

  val abstractEVarCtx :
    CompSyn.dProg -> IntSyn.exp -> IntSyn.sub ->
    IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.exp
    * TableParam.resEqn
    * IntSyn.sub

  val abstractAnswSub : IntSyn.sub -> IntSyn.dctx * IntSyn.sub
  val raiseType : IntSyn.dctx -> IntSyn.exp -> IntSyn.exp
end
