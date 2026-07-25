(* # 1 "src/terminate/Checking.sig.ml" *)
open! Basis

(* Reasoning about orders *)
(* Author: Brigitte Pientka *)

module type CHECKING = sig
  (*! structure IntSyn : INTSYN !*)
  module Order : ORDER

  (*! structure Paths : PATHS !*)
  (* If Q marks all parameters in a context G we write   G : Q  *)
  type quantifier = All | Exist | And of Paths.occ

  (* Quantifier to mark parameters *)
  (* Q ::= All                     *)
  (*     | Exist                     *)
  (*     | And                     *)
  type 'a predicate =
    | Less of 'a * 'a
    | Leq of 'a * 'a
    | Eq of 'a * 'a
    | Pi of IntSyn.dec * 'a predicate

  type nonrec order = (IntSyn.eclo * IntSyn.eclo) Order.order

  (* reduction predicate context (unordered) *)
  type nonrec rctx = order predicate list

  (* mixed-prefix context *)
  type nonrec qctx = quantifier IntSyn.ctx

  val shiftRCtx : rctx -> (IntSyn.sub -> IntSyn.sub) -> rctx

  val shiftPred :
    order predicate -> (IntSyn.sub -> IntSyn.sub) -> order predicate

  val deduce : IntSyn.dctx * qctx * rctx * order predicate -> bool
end
