(* # 1 "src/prover/Data.sig.ml" *)
open! Basis

(* Data Global parameters *)
(* Author: Carsten Schuermann *)

module type DATA = sig
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end
