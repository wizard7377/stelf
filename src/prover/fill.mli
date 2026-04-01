include module type of Fill_intf

module Fill (Fill__0 : sig
  module Data : Data.DATA

  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module State' : State.STATE

  (*! sharing State'.IntSyn = IntSyn' !*)
  (*! sharing State'.Tomega = Tomega' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  (*! sharing Abstract.Tomega = Tomega' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Search : Psearch.SEARCH

  (*! sharing Search.IntSyn = IntSyn' !*)
  (*! sharing Search.Tomega = Tomega' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY
end) : FILL with module State = Fill__0.State'
