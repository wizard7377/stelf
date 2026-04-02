include module type of TomegaUnify_intf

module TomegaUnify (TomegaUnify__0 : sig
  (* Unification on Formulas *)
  (* Author: Carsten Schuermann *)
  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn' !*)
  module Normalize : Normalize.NORMALIZE

  (*! sharing Normalize.IntSyn = IntSyn' !*)
  (*! sharing Normalize.Tomega = Tomega' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module TomegaPrint : Tomegaprint.TOMEGAPRINT

  (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
  (*! sharing TomegaPrint.Tomega = Tomega' !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module Weaken : Weaken_intf.WEAKEN
end) : TOMEGAUNIFY
