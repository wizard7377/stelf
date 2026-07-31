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

(* # 1 "src/opsem/Ptrecon.sig.ml" *)
open! Basis

(* Abstract Machine guided by proof skeleton *)
(* Author: Brigitte Pientks *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
(* Proof term reconstruction by proof skeleton *)

module type PTRECON = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  exception Error of string

  val solve :
    CompSyn.pskeleton
    * (CompSyn.goal * IntSyn.sub)
    * CompSyn.dProg
    * (CompSyn.pskeleton * IntSyn.exp -> unit) ->
    unit
end
