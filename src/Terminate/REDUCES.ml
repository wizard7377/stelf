open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
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
open! Subordinate
open! Subordinate
open! Paths
open! Paths.Paths_
open! Solvers
open! Solvers.Solvers_

(* # 1 "src/terminate/Reduces.sig.ml" *)
open! Basis

(* Reduction and Termination checker *)
(* Author: Brigitte Pientka *)

module type REDUCES = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string

  val reset : unit -> unit
  val checkFamReduction : IntSyn.cid -> unit
  val checkFam : IntSyn.cid -> unit
end
