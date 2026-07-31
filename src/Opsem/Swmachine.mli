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

(* # 1 "src/opsem/Swmachine.sig.ml" *)

(* # 1 "src/opsem/Swmachine.fun.ml" *)
open! Trace
open! Absmachine
open! Basis

module SwMachine (SwMachine__0 : sig
  module Trace : TRACE
  module AbsMachine : ABSMACHINE
  module TMachine : ABSMACHINE
end) : ABSMACHINE
