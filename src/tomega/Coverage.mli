include module type of Coverage_intf

module MakeTomegaCoverage
    (TomegaPrint : Tomegaprint.TOMEGAPRINT)
    (TomegaTypeCheck : TomegaTypecheck_intf.TOMEGATYPECHECK)
    (Cover : COVER) :
  TOMEGACOVERAGE
(*
  (* Coverage checker for programs *)
  (* Author: Carsten Schuermann *)
  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module TomegaPrint : Tomegaprint.TOMEGAPRINT

  (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
  (*! sharing TomegaPrint.Tomega = Tomega' !*)
  module TomegaTypeCheck : TomegaTypecheck_intf.TOMEGATYPECHECK

  (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
  (*! sharing TomegaTypeCheck.Tomega = Tomega' !*)
  module Cover : COVER
*)
