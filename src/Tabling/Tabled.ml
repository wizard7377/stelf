open! Basis
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Print
open! Print.Print_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Index
open! Index.Index_

(* # 1 "src/tabling/Tabled.sig.ml" *)

(* # 1 "src/tabling/Tabled.fun.ml" *)

(* # 1 "src/tabling/Tabled.sml.ml" *)
open! Basis

module TabledSyn =
  Tabledsyn.MakeTabledSyn (Names) (TableInstances.IntRedBlackTree) (Index)
