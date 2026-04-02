include module type of Typecheck_intf

module MakeTypeCheck
    (Conv : CONV)
    (Whnf : WHNF)
    (Names : NAMES)
    (Print : PRINT) :
  TYPECHECK
(*
  (*! structure IntSyn' : INTSYN !*)
  (*! sharing Conv.IntSyn = IntSyn' !*)
  (*! sharing Whnf.IntSyn = IntSyn'  !*)
  (*! sharing Names.IntSyn = IntSyn' !*)
*)

module type STRICT = Strict.STRICT
module TypeCheck : TYPECHECK
module Strict : STRICT
