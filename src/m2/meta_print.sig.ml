open! Basis
open Metasyn

(* Meta printer for proof states *)
(* Author: Carsten Schuermann *)
module type METAPRINT = sig
  module MetaSyn : METASYN

  val stateToString : MetaSyn.state_ -> string
  val sgnToString : MetaSyn.sgn_ -> string
  val modeToString : MetaSyn.mode_ -> string
  val conDecToString : IntSyn.conDec_ -> string
end
(* signature METAPRINT *)
