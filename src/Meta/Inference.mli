include module type of INFERENCE

module Inference (Inference__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn !*)
  module StateSyn' : STATESYN.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn !*)
  module FunTypeCheck : FUNTYPECHECK.FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
  module UniqueSearch : UNIQUESEARCH.UNIQUESEARCH

  (*! sharing UniqueSearch.IntSyn = IntSyn !*)
  (*! sharing UniqueSearch.FunSyn = FunSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module Whnf : WHNF
end) : INFERENCE.INFERENCE
