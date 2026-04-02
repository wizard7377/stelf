include module type of Typecheck_intf

module MakeTypeCheck (TypeCheck__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn'  !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Print : PRINT
end) : TYPECHECK

module type STRICT = Strict.STRICT
module TypeCheck : TYPECHECK
module Strict : STRICT
