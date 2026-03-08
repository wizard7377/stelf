open! Basis

(* Substitution Trees *)
(* Author: Brigitte Pientka *)
module type SUBTREE = sig
  open Red_black_set

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN     !*)
  (*! structure RBSet : RBSET  !*)
  type nonrec nvar = int

  (* index for normal variables *)
  type nonrec bvar = int

  (* index for bound variables *)
  type nonrec bdepth = int

  (* depth of locally bound variables *)
  (* normal (linear) substitutions *)
  (*  type normalSubsts = (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp) RBSet.ordSet *)
  type typeLabel = TypeLabel | Body
  type nonrec normalSubsts = (typeLabel * IntSyn.exp_) RBSet.ordSet

  type nonrec querySubsts =
    (IntSyn.dec_ IntSyn.ctx_ * (typeLabel * IntSyn.exp_)) RBSet.ordSet

  open Compsyn

  type cGoal_ =
    | CGoals of CompSyn.auxGoal_ * IntSyn.cid * CompSyn.conjunction_ * int

  (* assignable (linear) subsitutions *)
  type assSub_ = Assign of IntSyn.dec_ IntSyn.ctx_ * IntSyn.exp_
  type nonrec assSubsts = assSub_ RBSet.ordSet

  (* key = int = bvar *)
  type cnstr_ = Eqn of IntSyn.dec_ IntSyn.ctx_ * IntSyn.exp_ * IntSyn.exp_

  type tree_ =
    | Leaf of normalSubsts * IntSyn.dec_ IntSyn.ctx_ * cGoal_
    | Node of normalSubsts * tree_ RBSet.ordSet

  (*  type candidate = assSubsts * normalSubsts * cnstrSubsts * Cnstr * IntSyn.Dec IntSyn.Ctx * CGoal *)
  val indexArray : (int ref * tree_ ref) Array.array
  val sProgReset : unit -> unit

  val sProgInstall :
    IntSyn.cid * CompSyn.compHead_ * CompSyn.conjunction_ -> unit

  val matchSig :
    IntSyn.cid
    * IntSyn.dec_ IntSyn.ctx_
    * IntSyn.eclo
    * ((CompSyn.conjunction_ * IntSyn.sub_) * IntSyn.cid -> unit) ->
    unit
end
(*  val goalToString : string -> IntSyn.Dec IntSyn.Ctx * CompSyn.Goal * IntSyn.Sub -> string *)
(* signature SUBTREE *)
