(* # 1 "src/m2/Splitting.sig.ml" *)
open! Basis
open Metasyn

(* Splitting *)
(* Author: Carsten Schuermann *)

module type SPLITTING = sig
  module MetaSyn : Metasyn.METASYN

  exception Error of string

  type operator

  val expand : MetaSyn.state -> operator list
  val apply : operator -> MetaSyn.state list
  val var : operator -> int
  val menu : operator -> string
  val index : operator -> int
end
