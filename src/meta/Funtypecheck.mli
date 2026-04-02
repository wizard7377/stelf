include module type of Funtypecheck_intf

module FunTypeCheck (FunTypeCheck__0 : sig
  (* Type checking for functional proof term calculus *)
  (* Author: Carsten Schuermann *)
  (*! structure FunSyn' : FUNSYN !*)
  module StateSyn' : Statesyn_intf.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = FunSyn'.IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = FunSyn'.IntSyn !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = FunSyn'.IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = FunSyn'.IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = FunSyn'.IntSyn !*)
  module Subordinate : Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = FunSyn'.IntSyn !*)
  module Weaken : Weaken_intf.WEAKEN

  (*! sharing Weaken.IntSyn = FunSyn'.IntSyn   !*)
  module FunPrint : Funprint_intf.FUNPRINT
end) : Funtypecheck_intf.FUNTYPECHECK
