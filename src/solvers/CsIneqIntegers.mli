(* # 1 "src/solvers/CsIneqIntegers.sig.ml" *)

(* # 1 "src/solvers/CsIneqIntegers.fun.ml" *)
open! Basis

module CsIneqIntegers (CSIneqIntegers__0 : sig
  (* Solver for linear inequations, based on branch & bound *)
  (* Author: Roberto Virga *)
  module Integers : Integers.INTEGERS
  module Rationals : Rationals.RATIONALS with type Integers.int = Integers.int

  (*! structure IntSyn : INTSYN !*)
  module Trail : TRAIL
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  module SparseArray : SparseArray.SPARSE_ARRAY
  module SparseArray2 : SparseArray2.SPARSE_ARRAY2

  (*! structure CsManager : CS_MANAGER !*)
  (*! sharing CsManager.IntSyn = IntSyn !*)
  module CsEqIntegers :
    CsEqIntegers.CS_EQ_INTEGERS with type Integers.int = Integers.int

  (*! sharing CsEqIntegers.IntSyn = IntSyn !*)
  (*! sharing CsEqIntegers.CsManager = CsManager !*)
end) : Cs.CS