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

(* # 1 "src/terminate/Terminate_.sig.ml" *)

(* # 1 "src/terminate/Terminate_.fun.ml" *)

(* # 1 "src/terminate/Terminate_.sml.ml" *)
open! Basis
open Checking
open Reduces

module type CHECKING = CHECKING
module type REDUCES = REDUCES

module Checking : CHECKING
module Reduces : REDUCES
