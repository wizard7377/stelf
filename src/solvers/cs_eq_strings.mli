(* # 1 "src/solvers/cs_eq_strings.sig.ml" *)

(* # 1 "src/solvers/cs_eq_strings.fun.ml" *)
open! Basis

module Cs_eq_strings (CSEqStrings__0 : sig
  (* String Equation Solver *)
  (* Author: Roberto Virga *)
  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : Cs.CS
