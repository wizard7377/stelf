(* # 1 "src/prover/Prover_.sig.ml" *)

(* # 1 "src/prover/Prover_.fun.ml" *)

(* # 1 "src/prover/Prover_.sml.ml" *)
open! Basis

module State = State.State (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure Tomega' = Tomega !*)
  module Formatter = Formatter
end)

module Introduce : Introduce.INTRODUCE with module State = State =
Introduce.Introduce (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure Tomega' = Tomega !*)
  module TomegaNames = Tomeganames.TomegaNames
  module State' = State
end)

module Elim : Elim.ELIM with module State = State = Elim.Elim (struct
  module Data = Data.Data

  (*! structure IntSyn' = IntSyn !*)
  (*! structure Tomega' = Tomega !*)
  module State' = State
  module Whnf = Whnf
  module Abstract = Abstract
  module Unify = UnifyTrail
  module Constraints = Constraints
  module Index = Index
  module TypeCheck = TypeCheck
end)

module FixedPoint : Fixedpoint.FIXEDPOINT with module State = State =
Fixedpoint.FixedPoint (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure Tomega' = Tomega !*)
  module State' = State
end)

module Split : Split.SPLIT with module State = State = Split.Split (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  (*! structure Tomega' = Tomega !*)
  module State' = State
  module Whnf = Whnf
  module Abstract = Abstract
  module Unify = UnifyTrail
  module Constraints = Constraints
  module Index = Index
  module Names = Names
  module Print = Print
  module TypeCheck = TypeCheck
  module Subordinate = Subordinate.Subordinate_.Subordinate
end)

module Search = Psearch.Search (struct
  module Global = Global
  module Data = Data.Data

  (*! structure IntSyn' = IntSyn !*)
  (*! structure Tomega' = Tomega !*)
  module State' = State
  module Abstract = Abstract
  module Conv = Conv
  module CompSyn' = CompSyn.CompSyn
  module Compile = Compile
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Index = Index
  module Assign = Assign__
  module CPrint = CPrint
  module Print = Print
  module Names = Names
  module CsManager = CsManager
end)

module Fill : Fill.FILL with module State = State = Fill.Fill (struct
  module Data = Data.Data

  (*! structure IntSyn' = IntSyn !*)
  (*! structure Tomega' = Tomega !*)
  module State' = State
  module Whnf = Whnf
  module Abstract = Abstract
  module Unify = UnifyTrail
  module Constraints = Constraints
  module Index = Index
  module Search = Search
  module TypeCheck = TypeCheck
end)

module Weaken = Pweaken.Weaken (struct
  (*! structure IntSyn' = IntSyn !*) module Whnf = Whnf
end)

(*
structure Recurse = Recurse
  (structure Global = Global
   structure Data = Data
   structure State' = State
   structure Whnf = Whnf
   structure Conv = Conv
   structure Names = Names
   structure Subordinate = Subordinate
   structure Print = Print
   structure Formatter = Formatter
   structure TomegaPrint = TomegaPrint
   structure Abstract = Abstract
   structure Unify = UnifyTrail
   structure Constraints = Constraints
   structure Index = Index
   structure Search = Search
   structure TypeCheck = TypeCheck)
*)
module Interactive = Interactive.Interactive (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  (*! structure Tomega' = Tomega !*)
  module State' = State
  module Ring = Ring.Ring
  module Formatter = Formatter
  module Trail = Trail
  module Names = Names
  module Weaken = Weaken
  module ModeSyn = ModeSyn
  module WorldSyn = WorldSyn
  module Introduce = Introduce
  module FixedPoint = FixedPoint
  module Split = Split
  module Fill = Fill
  module Elim = Elim
end)
