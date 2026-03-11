open! Basis
open Meta_global

(* Global parameters *)
(* Author: Carsten Schuermann *)
module type MTPGLOBAL = sig
  type proverType_ = New | Old

  val prover : proverType_ ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end
(* signature MTPGLOBAL *)
