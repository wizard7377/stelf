(* # 1 "src/solvers/cs_ineq_field.sig.ml" *)

(* # 1 "src/solvers/cs_ineq_field.fun.ml" *)
open! Basis

module Cs_ineq_field (CSIneqField__0 : sig
  (* Solver for a linearly ordered field, based on the simplex method *)
  (* Author: Roberto Virga *)
  module OrderedField : Ordered_field.ORDERED_FIELD

  (*! structure IntSyn : INTSYN !*)
  module Trail : TRAIL
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  module SparseArray : Sparse_array.SPARSE_ARRAY
  module SparseArray2 : Sparse_array2.SPARSE_ARRAY2

  (*! structure Cs_manager : CS_MANAGER !*)
  (*! sharing Cs_manager.IntSyn = IntSyn !*)
  module Cs_eq_field :
    Cs_eq_field.CS_EQ_FIELD with type Field.number = OrderedField.number

  (*! sharing Cs_eq_field.IntSyn = IntSyn !*)
  (*! sharing Cs_eq_field.Cs_manager = Cs_manager !*)
end) : Cs.CS
