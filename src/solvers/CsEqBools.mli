(* # 1 "src/solvers/CsEqBools.sig.ml" *)

(* # 1 "src/solvers/CsEqBools.fun.ml" *)
open! Basis

module CsEqBools (CSEqBools__0 : sig
  (* Booleans Equation Solver *)
  (* Author: Roberto Virga *)
  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : Cs.CS
