(* # 1 "src/m2/MetaGlobal.sig.ml" *)
open! Basis

(* Global parameters *)
(* Author: Carsten Schuermann *)

module type METAGLOBAL = sig
  type strategy = Rfs | Frs [@@deriving eq, ord, show]

  val strategy : strategy ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end
