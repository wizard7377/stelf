include module type of Cs_eq_integers_intf

module Cs_eq_integers (CSEqIntegers__0 : sig
  (* Diophantine Equation Solver *)
  (* Author: Roberto Virga *)
  module Integers : Integers.INTEGERS

  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : CS_EQ_INTEGERS with type Integers.int = CSEqIntegers__0.Integers.int
