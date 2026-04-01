(* # 1 "src/m2/strategy.sig.ml" *)
open! Basis
open Metasyn

(* Strategy *)
(* Author: Carsten Schuermann *)

module type STRATEGY = sig
  module MetaSyn : Metasyn.METASYN

  val run : MetaSyn.state list -> MetaSyn.state list * MetaSyn.state list
end
