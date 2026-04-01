include module type of Cs_eq_field_intf

module Cs_eq_field (CSEqField__0 : sig
  (* Gaussian-Elimination Equation Solver *)
  (* Author: Roberto Virga *)
  module Field : Field.FIELD

  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : CS_EQ_FIELD with type Field.number = CSEqField__0.Field.number
