(* # 1 "src/m2/Recursion.sig.ml" *)
open! Basis
open Metasyn

(* Recursion *)
(* Author: Carsten Schuermann *)

module type RECURSION = sig
  module MetaSyn : Metasyn.METASYN

  exception Error of string

  type operator

  val expandLazy : MetaSyn.state -> operator list
  val expandEager : MetaSyn.state -> operator list
  val apply : operator -> MetaSyn.state
  val menu : operator -> string
end
