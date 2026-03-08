open! Basis

(* Gaussian-Elimination Equation Solver *)
(* Author: Roberto Virga *)
module type CS_EQ_INTEGERS = sig
  include Cs.CS
  module Integers : Integers.INTEGERS

  (*! structure IntSyn : INTSYN !*)
  (* Foreign expressions *)
  type nonrec 'a mset = 'a list

  (* MultiSet                   *)
  type sum_ = Sum of Integers.int * mon_ mset
  and mon_ = Mon of Integers.int * (IntSyn.exp_ * IntSyn.sub_) mset

  (* Sum :                      *)
  (* Sum ::= m + M1 + ...       *)
  (* Monomials:                 *)
  (* Mon ::= n * U1[s1] * ...   *)
  val fromExp : IntSyn.eclo -> sum_
  val toExp : sum_ -> IntSyn.exp_
  val normalize : sum_ -> sum_
  val compatibleMon : mon_ * mon_ -> bool

  (* Internal expressions constructors *)
  val number : unit -> IntSyn.exp_
  val unaryMinus : IntSyn.exp_ -> IntSyn.exp_
  val plus : IntSyn.exp_ * IntSyn.exp_ -> IntSyn.exp_
  val minus : IntSyn.exp_ * IntSyn.exp_ -> IntSyn.exp_
  val times : IntSyn.exp_ * IntSyn.exp_ -> IntSyn.exp_
  val constant : Integers.int -> IntSyn.exp_
end
(* signature CS_EQ_FIELD *)
