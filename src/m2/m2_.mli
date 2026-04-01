(* # 1 "src/m2/m2_.sig.ml" *)

(* # 1 "src/m2/m2_.fun.ml" *)

(* # 1 "src/m2/m2_.sml.ml" *)
open! Basis
open Meta_print
open Init
open Search
open Lemma
open Splitting
open Filling
open Recursion
open Qed
open Strategy
open Prover
open Mpi
open Skolem

module Skolem : Skolem_intf.SKOLEM
module IndexSkolem : Index_intf.INDEX

module M2Prover : Prover_intf.PROVER
