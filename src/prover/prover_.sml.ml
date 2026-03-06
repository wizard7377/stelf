open! Basis;;
module State = (State)(struct
                         (*! structure IntSyn' = IntSyn !*);;
                         (*! structure Tomega' = Tomega !*);;
                         module WorldSyn' = WorldSyn;;
                         module Formatter = Formatter;;
                         end);;
module Introduce = (Introduce)(struct
                                 (*! structure IntSyn' = IntSyn !*);;
                                 (*! structure Tomega' = Tomega !*);;
                                 module TomegaNames = TomegaNames;;
                                 module State' = State;;
                                 end);;
module Elim = (Elim)(struct
                       module Data = Data;;
                       (*! structure IntSyn' = IntSyn !*);;
                       (*! structure Tomega' = Tomega !*);;
                       module State' = State;;
                       module Whnf = Whnf;;
                       module Abstract = Abstract;;
                       module Unify = UnifyTrail;;
                       module Constraints = Constraints;;
                       module Index = Index;;
                       module TypeCheck = TypeCheck;;
                       end);;
module FixedPoint = (FixedPoint)(struct
                                   (*! structure IntSyn' = IntSyn !*);;
                                   (*! structure Tomega' = Tomega !*);;
                                   module State' = State;;
                                   end);;
module Split = (Split)(struct
                         module Global = Global;;
                         (*! structure IntSyn' = IntSyn !*);;
                         (*! structure Tomega' = Tomega !*);;
                         module State' = State;;
                         module Whnf = Whnf;;
                         module Abstract = Abstract;;
                         module Unify = UnifyTrail;;
                         module Constraints = Constraints;;
                         module Index = Index;;
                         module Names = Names;;
                         module Print = Print;;
                         module TypeCheck = TypeCheck;;
                         module Subordinate = Subordinate;;
                         end);;
module Search = (Search)(struct
                           module Global = Global;;
                           module Data = Data;;
                           (*! structure IntSyn' = IntSyn !*);;
                           (*! structure Tomega' = Tomega !*);;
                           module State' = State;;
                           module Abstract = Abstract;;
                           module Conv = Conv;;
                           module CompSyn' = CompSyn;;
                           module Compile = Compile;;
                           module Whnf = Whnf;;
                           module Unify = UnifyTrail;;
                           module Index = IndexSkolem;;
                           module Assign = Assign;;
                           module CPrint = CPrint;;
                           module Print = Print;;
                           module Names = Names;;
                           module CSManager = CSManager;;
                           end);;
module Fill = (Fill)(struct
                       module Data = Data;;
                       (*! structure IntSyn' = IntSyn !*);;
                       (*! structure Tomega' = Tomega !*);;
                       module State' = State;;
                       module Whnf = Whnf;;
                       module Abstract = Abstract;;
                       module Unify = UnifyTrail;;
                       module Constraints = Constraints;;
                       module Index = Index;;
                       module Search = Search;;
                       module TypeCheck = TypeCheck;;
                       end);;
module Weaken = (Weaken)(struct
                           (*! structure IntSyn' = IntSyn !*);;
                           module Whnf = Whnf;;
                           end);;
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
*);;
module Interactive = (Interactive)(struct
                                     module Global = Global;;
                                     (*! structure IntSyn' = IntSyn !*);;
                                     (*! structure Tomega' = Tomega !*);;
                                     module State' = State;;
                                     module Ring = Ring;;
                                     module Formatter = Formatter;;
                                     module Trail = Trail;;
                                     module Names = Names;;
                                     module Weaken = Weaken;;
                                     module ModeSyn = ModeSyn;;
                                     module WorldSyn = WorldSyn;;
                                     module Introduce = Introduce;;
                                     module FixedPoint = FixedPoint;;
                                     module Split = Split;;
                                     module Fill = Fill;;
                                     module Elim = Elim;;
                                     end);;