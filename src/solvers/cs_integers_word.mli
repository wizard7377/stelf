(* # 1 "src/solvers/cs_integers_word.sig.ml" *)

(* # 1 "src/solvers/cs_integers_word.fun.ml" *)
open! Basis

module Cs_int_word (CSIntWord__0 : sig
  (* Solver for machine integers *)
  (* Author: Roberto Virga *)
  (*! structure IntSyn : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  (*! structure Cs_manager : CS_MANAGER !*)
  (*! sharing Cs_manager.IntSyn = IntSyn !*)
  val wordSize : int
end) : Cs.CS
