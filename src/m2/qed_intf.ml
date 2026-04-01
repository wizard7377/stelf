(* # 1 "src/m2/qed.sig.ml" *)
open! Basis
open Metasyn

(* Qed *)
(* Author: Carsten Schuermann *)

module type QED = sig
  module MetaSyn : Metasyn.METASYN

  exception Error of string

  val subgoal : MetaSyn.state -> bool
end
