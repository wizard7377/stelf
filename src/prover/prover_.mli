(* # 1 "src/prover/prover_.sig.ml" *)

(* # 1 "src/prover/prover_.fun.ml" *)

(* # 1 "src/prover/prover_.sml.ml" *)
open! Basis

module State : State.STATE

module Introduce : Introduce.INTRODUCE with module State = State

module Elim : Elim.ELIM with module State = State

module FixedPoint : Fixedpoint.FIXEDPOINT with module State = State

module Split : Split.SPLIT with module State = State

module Fill : Fill.FILL with module State = State
