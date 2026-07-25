(* # 1 "src/domains/Rationals.sig.ml" *)
open Basis
open OrderedField
open Integers

(* Rational numbers *)
(* Author: Roberto Virga *)

module type RATIONALS = sig
  include ORDERED_FIELD
  module Integers : INTEGERS

  (* Conversions between rationals and integers *)
  val fromInteger : Integers.int -> number
  val floor : number -> Integers.int
  val ceiling : number -> Integers.int

  (* Basic projections *)
  val numerator : number -> Integers.int
  val denominator : number -> Integers.int
end
