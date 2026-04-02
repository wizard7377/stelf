(* # 1 "src/tomega/Tomega_.sig.ml" *)

(* # 1 "src/tomega/Tomega_.fun.ml" *)

(* # 1 "src/tomega/Tomega_.sml.ml" *)
open! Basis
module Tomega = Lambda_.Tomega

module TomegaAbstract = TomegaAbstract.TomegaAbstract (struct
  module Global = Global

  let abstract_raiseType = Abstract.raiseType
  let abstract_raiseTerm = Abstract.raiseTerm

  module Whnf = Whnf
  module Subordinate = Subordinate_.Subordinate
end)

module TomegaPrint = Tomegaprint.TomegaPrint (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure Tomega' = Tomega !*)
  module Formatter = Print_.Print.Formatter
  module Names = Names_.Names
  module Print : PRINT with module Formatter = Formatter = Print_.Print
end)

module Weaken = Weaken.Make_Weaken (struct
  module Whnf = Whnf
end)

module TomegaTypeCheck = TomegaTypecheck.TomegaTypeCheck (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  module Abstract = Abstract

  (*! structure Tomega' = Tomega !*)
  module TypeCheck = TypeCheck
  module Conv = Conv
  module Whnf = Whnf
  module Subordinate = Subordinate_.Subordinate
  module TomegaPrint = TomegaPrint
  module Print = Print
  module Weaken = Weaken
  module TomegaAbstract = TomegaAbstract
end)

(* structure TomegaUnify = TomegaUnify
  (structure Global = Global
   ! structure IntSyn' = IntSyn !
   structure Abstract = Abstract
   ! structure Tomega' = Tomega !
   structure TypeCheck = TypeCheck
   structure Normalize = Normalize
   structure Conv = Conv
   structure Whnf = Whnf
   structure Subordinate = Subordinate
   structure TomegaPrint = TomegaPrint
   structure Print = Print
   structure Weaken = Weaken);
*)
module Opsem_ = Opsem.MakeOpsem (struct
  module Global = Global
  module IntSyn' = IntSyn
  module Abstract = Abstract
  module Tomega' = Tomega
  module TypeCheck = TypeCheck
  module Unify = UnifyNoTrail
  module Conv = Conv
  module Whnf = Whnf
  module Print = Print
  module Subordinate = Subordinate_.Subordinate
  module TomegaPrint = TomegaPrint
  module TomegaTypeCheck = TomegaTypeCheck
  module Weaken = Weaken
end)

(*
structure Opsem = OpsemCont
  (structure Global = Global
   structure IntSyn' = IntSyn
   structure Abstract = Abstract
   structure Tomega' = Tomega
   structure TypeCheck = TypeCheck
   structure Normalize = Normalize
   structure Unify = UnifyNoTrail
   structure Conv = Conv
   structure Whnf = Whnf
   structure Print = Print
   structure Subordinate = Subordinate
   structure TomegaPrint = TomegaPrint
   structure TomegaTypeCheck = TomegaTypeCheck
   structure Weaken = Weaken);
*)
module Redundant = Redundant.Redundant (struct
  module Opsem = Opsem_
end)

module Converter_ = Converter.MakeConverter (struct
  module Global = Global
  module IntSyn' = IntSyn
  module Abstract = Abstract
  module Tomega' = Tomega
  module Names = Names
  module ModeTable = ModeTable
  module TypeCheck = TypeCheck
  module TomegaAbstract = TomegaAbstract
  module TomegaTypeCheck = TomegaTypeCheck
  module Trail = Trail
  module Unify = UnifyTrail
  module TomegaPrint = TomegaPrint
  module Whnf = Whnf
  module WorldSyn = WorldSyn
  module Worldify = Worldify
  module Subordinate = Subordinate_.Subordinate
  module Print = Print
  module Redundant = Redundant
  module Weaken = Weaken
end)

module TomegaCoverage_ = Coverage.MakeTomegaCoverage (struct
  module Global = Global
  module IntSyn' = IntSyn
  module Tomega' = Tomega
  module TomegaPrint = TomegaPrint
  module TomegaTypeCheck = TomegaTypeCheck
  module Cover = Cover_.Cover
end)

module Opsem = Opsem_
module Converter = Converter_
module TomegaCoverage = TomegaCoverage_

