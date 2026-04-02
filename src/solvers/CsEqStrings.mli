(* # 1 "src/solvers/CsEqStrings.sig.ml" *)

(* # 1 "src/solvers/CsEqStrings.fun.ml" *)
open! Basis

module CsEqStrings (CSEqStrings__0 : sig
  (* String Equation Solver *)
  (* Author: Roberto Virga *)
  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : Cs.CS
