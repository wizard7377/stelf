(* # 1 "src/solvers/CsEqIntegers.sig.ml" *)
open! Basis

(* Gaussian-Elimination Equation Solver *)
(* Author: Roberto Virga *)

module type CS_EQ_INTEGERS = sig
  include Cs.CS
  module Integers : Integers.INTEGERS

  (*! structure IntSyn : INTSYN !*)
  (* Foreign expressions *)
  type 'a mset = 'a list

  (* MultiSet                   *)
  type sum_ = Sum of Integers.int * mon_ mset
  and mon_ = Mon of Integers.int * (IntSyn.exp * IntSyn.sub) mset

  (* Sum :                      *)
  (* Sum ::= m + M1 + ...       *)
  (* Monomials:                 *)
  (* Mon ::= n * U1[s1] * ...   *)
  val fromExp : IntSyn.eclo -> sum_
  val toExp : sum_ -> IntSyn.exp
  val normalize : sum_ -> sum_
  val compatibleMon : mon_ * mon_ -> bool

  (* Internal expressions constructors *)
  val number : unit -> IntSyn.exp
  val unaryMinus : IntSyn.exp -> IntSyn.exp
  val plus : IntSyn.exp * IntSyn.exp -> IntSyn.exp
  val minus : IntSyn.exp * IntSyn.exp -> IntSyn.exp
  val times : IntSyn.exp * IntSyn.exp -> IntSyn.exp
  val constant : Integers.int -> IntSyn.exp
end
