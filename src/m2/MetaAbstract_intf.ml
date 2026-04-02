(* # 1 "src/m2/MetaAbstract.sig.ml" *)
open! Basis
open Metasyn

(* Meta Abstraction *)
(* Author: Carsten Schuermann *)

module type METAABSTRACT = sig
  module MetaSyn : Metasyn.METASYN

  exception Error of string

  val abstract : MetaSyn.state -> MetaSyn.state
end
