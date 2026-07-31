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

(* # 1 "src/worldcheck/Worldcheck_.sig.ml" *)

(* # 1 "src/worldcheck/Worldcheck_.fun.ml" *)

(* # 1 "src/worldcheck/Worldcheck_.sml.ml" *)
open! Basis

module type WORLDIFY = WORLDIFY.WORLDIFY
module type WORLDSYN = WORLDSYN.WORLDSYN

module WorldSyn : WORLDSYN
module Worldify : WORLDIFY
