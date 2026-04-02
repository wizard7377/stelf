include module type of CsEqIntegers_intf

module CsEqIntegers (CSEqIntegers__0 : sig
  (* Diophantine Equation Solver *)
  (* Author: Roberto Virga *)
  module Integers : Integers.INTEGERS

  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : CS_EQ_INTEGERS with type Integers.int = CSEqIntegers__0.Integers.int
