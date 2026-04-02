include module type of Psearch_intf

module Search (Search__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module State' : State.STATE

  (*! sharing State'.IntSyn = IntSyn' !*)
  (*! sharing State'.Tomega = Tomega' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  (*! sharing Abstract.Tomega = Tomega' !*)
  module Data : Data.DATA
  module CompSyn' : CompSyn_intf.COMPSYN

  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Assign : Assign_intf.ASSIGN

  (*! sharing Assign.IntSyn = IntSyn' !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module Compile : Compile_intf.COMPILE

  (*! sharing Compile.IntSyn = IntSyn' !*)
  (*! sharing Compile.CompSyn = CompSyn' !*)
  module CPrint : Cprint_intf.CPRINT

  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module CsManager : CsManager.CS_MANAGER
end) : SEARCH
