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

module Weaken = Weaken.Make_Weaken (Whnf)

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
module Opsem_ =
  Opsem.MakeOpsem
    (Whnf)
    (Abstract)
    (Subordinate_.Subordinate)
    (TomegaTypeCheck)
    (TomegaPrint)
    (UnifyNoTrail)

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

module Converter_ =
  Converter.MakeConverter
    (Global)
    (Abstract)
    (ModeTable)
    (Names)
    (UnifyTrail)
    (Whnf)
    (Print)
    (TomegaPrint)
    (WorldSyn)
    (Worldify)
    (TomegaTypeCheck)
    (Subordinate_.Subordinate)
    (TypeCheck)
    (Redundant)
    (TomegaAbstract)

module TomegaCoverage_ =
  Coverage.MakeTomegaCoverage
    (TomegaPrint)
    (TomegaTypeCheck)
    (Cover_.Cover)

module Opsem = Opsem_
module Converter = Converter_
module TomegaCoverage = TomegaCoverage_

