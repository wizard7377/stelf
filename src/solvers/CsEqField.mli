include module type of CsEqField_intf

module CsEqField (CSEqField__0 : sig
  (* Gaussian-Elimination Equation Solver *)
  (* Author: Roberto Virga *)
  module Field : Field.FIELD

  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : CS_EQ_FIELD with type Field.number = CSEqField__0.Field.number
