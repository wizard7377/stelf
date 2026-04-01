(* # 1 "src/compile/subtree.sig.ml" *)
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
  type typeLabel = TypeLabel | Body [@@deriving eq, ord, show]
  type nonrec normalSubsts = (typeLabel * IntSyn.exp) RBSet.ordSet

  type nonrec querySubsts =
    (IntSyn.dec IntSyn.ctx * (typeLabel * IntSyn.exp)) RBSet.ordSet

  open CompSyn

  type cGoal =
    | CGoals of CompSyn.auxGoal * IntSyn.cid * CompSyn.conjunction * int

  (* assignable (linear) subsitutions *)
  type assSub = Assign of IntSyn.dec IntSyn.ctx * IntSyn.exp
  type nonrec assSubsts = assSub RBSet.ordSet

  (* key = int = bvar *)
  type cnstr = Eqn of IntSyn.dec IntSyn.ctx * IntSyn.exp * IntSyn.exp

  type tree =
    | Leaf of normalSubsts * IntSyn.dec IntSyn.ctx * cGoal
    | Node of normalSubsts * tree RBSet.ordSet

  (*  type candidate = assSubsts * normalSubsts * cnstrSubsts * Cnstr * IntSyn.Dec IntSyn.Ctx * CGoal *)
  val indexArray : (int ref * tree ref) Array.array
  val sProgReset : unit -> unit
  val sProgInstall : IntSyn.cid * CompSyn.compHead * CompSyn.conjunction -> unit

  val matchSig :
    IntSyn.cid
    * IntSyn.dec IntSyn.ctx
    * IntSyn.eclo
    * ((CompSyn.conjunction * IntSyn.sub) * IntSyn.cid -> unit) ->
    unit
end
