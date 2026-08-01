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

(* # 1 "src/worldcheck/WorldSyn.sig.ml" *)
open! Basis

(* World Checking *)
(* Author: Carsten Schuermann *)

module type WORLDSYN = sig
  exception Error of string

  val reset : unit -> unit
  val install : IntSyn.cid -> Tomega.worlds -> unit
  val lookup : IntSyn.cid -> Tomega.worlds

  (* raises Error if undeclared *)
  val uninstall : IntSyn.cid -> bool

  (* true if declared *)
  val worldcheck : Tomega.worlds -> IntSyn.cid -> unit
  val ctxToList : IntSyn.dec IntSyn.ctx -> IntSyn.dec list
  val isSubsumed : Tomega.worlds -> IntSyn.cid -> unit
  val getWorlds : IntSyn.cid -> Tomega.worlds
end
