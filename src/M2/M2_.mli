(* # 1 "src/m2/M2_.sig.ml" *)

(* # 1 "src/m2/M2_.fun.ml" *)

(* # 1 "src/m2/M2_.sml.ml" *)
open! Basis
open MetaPrint
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
module Skolem : SKOLEM.SKOLEM
module IndexSkolem : INDEX.INDEX
module M2Prover : PROVER.PROVER
