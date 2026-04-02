include module type of Converter_intf

module MakeConverter (Converter__0 : sig
  (* Converter from relational representation to a functional
   representation of proof terms *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing ModeSyn.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module TomegaPrint : Tomegaprint.TOMEGAPRINT

  (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
  (*! sharing TomegaPrint.Tomega = Tomega' !*)
  module WorldSyn : Worldcheck_.WORLDSYN

  (*! sharing WorldSyn.IntSyn = IntSyn' !*)
  (*! sharing WorldSyn.Tomega = Tomega' !*)
  module Worldify : Worldcheck_.WORLDIFY

  (*! sharing Worldify.IntSyn = IntSyn' !*)
  (*! sharing Worldify.Tomega = Tomega' !*)
  module TomegaTypeCheck : TomegaTypecheck_intf.TOMEGATYPECHECK

  (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
  (*! sharing TomegaTypeCheck.Tomega = Tomega' !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module TypeCheck : Typecheck_.TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Redundant : Redundant_intf.REDUNDANT
  module TomegaAbstract : TomegaAbstract_intf.TOMEGAABSTRACT
end) : CONVERTER
