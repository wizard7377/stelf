(* # 1 "src/meta/global.sig.ml" *)
open! Basis
open Meta_global

(* Global parameters *)
(* Author: Carsten Schuermann *)

module type MTPGLOBAL = sig
  type proverType = New | Old [@@deriving eq, ord, show]

  val prover : proverType ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end
