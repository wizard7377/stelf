(* # 1 "src/m2/meta_print.sig.ml" *)
open! Basis
open Metasyn

(* Meta printer for proof states *)
(* Author: Carsten Schuermann *)

module type METAPRINT = sig
  module MetaSyn : Metasyn.METASYN

  val stateToString : MetaSyn.state -> string
  val sgnToString : MetaSyn.sgn -> string
  val modeToString : MetaSyn.mode -> string
  val conDecToString : IntSyn.conDec -> string
end
