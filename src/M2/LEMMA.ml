(* # 1 "src/m2/Lemma.sig.ml" *)
open! Basis
open Metasyn

(* Lemma *)
(* Author: Carsten Schuermann *)

module type LEMMA = sig
  module MetaSyn : Metasyn.METASYN

  exception Error of string

  val apply : MetaSyn.state * IntSyn.cid -> MetaSyn.state
end
