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

(* # 1 "src/opsem/AbsmachineSbt.sig.ml" *)
open! Basis

(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

module type ABSMACHINESBT = sig
  (*! structure IntSyn  : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  val solve :
    (CompSyn.goal * IntSyn.sub)
    * CompSyn.dProg
    * (CompSyn.flatterm list -> unit) ->
    unit
end
