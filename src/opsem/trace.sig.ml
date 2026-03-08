open! Basis

module type TRACE = sig
  (* Program interface *)
  (*! structure IntSyn : INTSYN !*)
  type nonrec goalTag

  val tagGoal : unit -> goalTag

  type event_ =
    | IntroHyp of IntSyn.head_ * IntSyn.dec_
    | DischargeHyp of IntSyn.head_ * IntSyn.dec_
    | IntroParm of IntSyn.head_ * IntSyn.dec_
    | DischargeParm of IntSyn.head_ * IntSyn.dec_
    | Resolved of IntSyn.head_ * IntSyn.head_
    | Subgoal of (IntSyn.head_ * IntSyn.head_) * (unit -> int)
    | SolveGoal of goalTag * IntSyn.head_ * IntSyn.exp_
    | SucceedGoal of goalTag * (IntSyn.head_ * IntSyn.head_) * IntSyn.exp_
    | CommitGoal of goalTag * (IntSyn.head_ * IntSyn.head_) * IntSyn.exp_
    | RetryGoal of goalTag * (IntSyn.head_ * IntSyn.head_) * IntSyn.exp_
    | FailGoal of goalTag * IntSyn.head_ * IntSyn.exp_
    | Unify of (IntSyn.head_ * IntSyn.head_) * IntSyn.exp_ * IntSyn.exp_
    | FailUnify of (IntSyn.head_ * IntSyn.head_) * string

  (* resolved with clause c, fam a *)
  (* clause c, fam a, nth subgoal *)
  (* clause head == goal *)
  (* failure message *)
  val signal : IntSyn.dctx * event_ -> unit
  val init : unit -> unit

  (* initialize trace, break and tag *)
  val tracing : unit -> bool

  (* currently tracing or using breakpoints *)
  (* User interface *)
  type 'a spec_ = None | Some of 'a list | All

  val trace : string spec_ -> unit
  val break : string spec_ -> unit
  val detail : int ref

  (* 0 = none, 1 = default, 2 = unify *)
  val show : unit -> unit

  (* show trace, break, detail *)
  val reset : unit -> unit
end
(* reset trace, break, detail *)
(* signature TRACE *)
