(* # 1 "src/solvers/CsIntegersWord.sig.ml" *)

(* # 1 "src/solvers/CsIntegersWord.fun.ml" *)
open! Basis

module Cs_int_word (CSIntWord__0 : sig
  (* Solver for machine integers *)
  (* Author: Roberto Virga *)
  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  (*! structure CsManager : CS_MANAGER !*)
  (*! sharing CsManager.IntSyn = IntSyn !*)
  val wordSize : int
end) : Cs.CS
