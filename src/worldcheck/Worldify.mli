include module type of Worldify_intf

module Worldify (Worldify__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  (*! sharing Tomega.IntSyn = IntSyn !*)
  module WorldSyn : WorldSyn.WORLDSYN

  (*! sharing WorldSyn.IntSyn = IntSyn !*)
  (*! sharing WorldSyn.Tomega = Tomega !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn !*)
  module CsManager : CsManager.CS_MANAGER

  (*! sharing CsManager.IntSyn = IntSyn !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module Table : TABLE
  module MemoTable : TABLE
  module IntSet : Intset.INTSET

  (*! structure Paths : PATHS !*)
  module Origins : Origins.ORIGINS
end) : WORLDIFY
