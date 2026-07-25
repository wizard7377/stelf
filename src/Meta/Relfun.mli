include module type of RELFUN

module RelFun (RelFun__0 : sig
  (* Converter from relational representation to a functional
   representation of proof terms *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure FunSyn' : FUNSYN !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing ModeSyn.IntSyn = FunSyn'.IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = FunSyn'.IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = FunSyn'.IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = FunSyn'.IntSyn !*)
  module Weaken : WEAKEN.WEAKEN

  (*! sharing Weaken.IntSyn = FunSyn'.IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = FunSyn'.IntSyn !*)
  module FunWeaken : FUNWEAKEN.FUNWEAKEN

  (*! sharing FunWeaken.FunSyn = FunSyn' !*)
  module FunNames : FUNNAMES.FUNNAMES
end) : RELFUN.RELFUN
