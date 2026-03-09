open! Basis
open Metasyn

(* Lemma *)
(* Author: Carsten Schuermann *)
module type LEMMA = sig
  module MetaSyn : METASYN

  exception Error of string

  val apply : MetaSyn.state_ * IntSyn.cid -> MetaSyn.state_
end
(* signature LEMMA *)
