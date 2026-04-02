(* # 1 "src/meta/Global.sig.ml" *)
open! Basis
open MetaGlobal

(* Global parameters *)
(* Author: Carsten Schuermann *)

module type MTPGLOBAL = sig
  type proverType = New | Old [@@deriving eq, ord, show]

  val prover : proverType ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end
