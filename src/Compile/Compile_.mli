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
include module type of COMPILE

module MakeCompile
    (Whnf : WHNF)
    (TypeCheck : TYPECHECK)
    (SubTree : Subtree.SUBTREE)
    (CPrint : Cprint.CPRINT)
    (Print : PRINT)
    (Names : NAMES) : COMPILE
(*
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  (*! sharing Whnf.IntSyn = IntSyn' !*)
  (* sharing TypeCheck.IntSyn = IntSyn' !*)
  (*! sharing SubTree.IntSyn = IntSyn' !*)
  (*! sharing SubTree.CompSyn = CompSyn' !*)
  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn' !*)
  (*! sharing Print.IntSyn = IntSyn' !*)
*)

module CPrint : Cprint.CPRINT
module SubTree : Subtree.SUBTREE
module Compile : COMPILE
module Assign__ : Assign.ASSIGN
