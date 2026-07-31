open! Basis
open! Trail
open! Trail.Trail_
open! Global
open! Global.Global_
open! Domains
open! Domains.Domains_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Modes
open! Modes.Modes_
open! Table
open! Table.Table_
open! Print
open! Print.Print_
open! Formatter
open! Formatter__Formatter_

(* # 1 "src/solvers/Cs.sig.ml" *)
open! Basis

(* Constraint Solver *)

module type CS = sig
  (*! structure CsManager : CS_MANAGER !*)
  (* all a constraint solver must define is a structure
     suitable for the constraint solver manager to install.
  *)
  val solver : CsManager.solver
end
