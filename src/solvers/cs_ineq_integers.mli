(* # 1 "src/solvers/cs_ineq_integers.sig.ml" *)

(* # 1 "src/solvers/cs_ineq_integers.fun.ml" *)
open! Basis

module Cs_ineq_integers (CSIneqIntegers__0 : sig
  (* Solver for linear inequations, based on branch & bound *)
  (* Author: Roberto Virga *)
  module Integers : Integers.INTEGERS
  module Rationals : Rationals.RATIONALS with type Integers.int = Integers.int

  (*! structure IntSyn : INTSYN !*)
  module Trail : TRAIL
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  module SparseArray : Sparse_array.SPARSE_ARRAY
  module SparseArray2 : Sparse_array2.SPARSE_ARRAY2

  (*! structure Cs_manager : CS_MANAGER !*)
  (*! sharing Cs_manager.IntSyn = IntSyn !*)
  module Cs_eq_integers :
    Cs_eq_integers.CS_EQ_INTEGERS with type Integers.int = Integers.int

  (*! sharing Cs_eq_integers.IntSyn = IntSyn !*)
  (*! sharing Cs_eq_integers.Cs_manager = Cs_manager !*)
end) : Cs.CS