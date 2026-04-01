(* # 1 "src/m2/init.sig.ml" *)
open! Basis
open Metasyn

(* Initialization *)
(* Author: Carsten Schuermann *)

module type INIT = sig
  module MetaSyn : Metasyn.METASYN

  exception Error of string

  val init : IntSyn.cid list -> MetaSyn.state list
end
