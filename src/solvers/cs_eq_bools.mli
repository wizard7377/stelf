(* # 1 "src/solvers/cs_eq_bools.sig.ml" *)

(* # 1 "src/solvers/cs_eq_bools.fun.ml" *)
open! Basis

module Cs_eq_bools (CSEqBools__0 : sig
  (* Booleans Equation Solver *)
  (* Author: Roberto Virga *)
  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : Cs.CS
