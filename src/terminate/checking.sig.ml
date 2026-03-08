open! Basis

(* Reasoning about orders *)
(* Author: Brigitte Pientka *)
module type CHECKING = sig
  (*! structure IntSyn : INTSYN !*)
  module Order : ORDER

  (*! structure Paths : PATHS !*)
  (* If Q marks all parameters in a context G we write   G : Q  *)
  type quantifier_ = All | Exist | And of Paths.occ

  (* Quantifier to mark parameters *)
  (* Q ::= All                     *)
  (*     | Exist                     *)
  (*     | And                     *)
  type 'a predicate_ =
    | Less of 'a * 'a
    | Leq of 'a * 'a
    | Eq of 'a * 'a
    | Pi of IntSyn.dec_ * 'a predicate_

  type nonrec order = (IntSyn.eclo * IntSyn.eclo) Order.order_

  (* reduction predicate context (unordered) *)
  type nonrec rctx = order predicate_ list

  (* mixed-prefix context *)
  type nonrec qctx = quantifier_ IntSyn.ctx_

  val shiftRCtx : rctx -> (IntSyn.sub_ -> IntSyn.sub_) -> rctx

  val shiftPred :
    order predicate_ -> (IntSyn.sub_ -> IntSyn.sub_) -> order predicate_

  val deduce : IntSyn.dctx * qctx * rctx * order predicate_ -> bool
end
(* signature CHECKING *)
