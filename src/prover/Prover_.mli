(* # 1 "src/prover/Prover_.sig.ml" *)

(* # 1 "src/prover/Prover_.fun.ml" *)

(* # 1 "src/prover/Prover_.sml.ml" *)
open! Basis

module State : State.STATE

module Introduce : Introduce.INTRODUCE with module State = State

module Elim : Elim.ELIM with module State = State

module FixedPoint : Fixedpoint.FIXEDPOINT with module State = State

module Split : Split.SPLIT with module State = State

module Fill : Fill.FILL with module State = State
