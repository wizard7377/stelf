(* # 1 "src/opsem/trace.sig.ml" *)
open! Basis

module type TRACE = sig
  (* Program interface *)
  (*! structure IntSyn : INTSYN !*)
  type goalTag

  val tagGoal : unit -> goalTag

  type event =
    | IntroHyp of IntSyn.head * IntSyn.dec
    | DischargeHyp of IntSyn.head * IntSyn.dec
    | IntroParm of IntSyn.head * IntSyn.dec
    | DischargeParm of IntSyn.head * IntSyn.dec
    | Resolved of IntSyn.head * IntSyn.head
    | Subgoal of (IntSyn.head * IntSyn.head) * (unit -> int)
    | SolveGoal of goalTag * IntSyn.head * IntSyn.exp
    | SucceedGoal of goalTag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | CommitGoal of goalTag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | RetryGoal of goalTag * (IntSyn.head * IntSyn.head) * IntSyn.exp
    | FailGoal of goalTag * IntSyn.head * IntSyn.exp
    | Unify of (IntSyn.head * IntSyn.head) * IntSyn.exp * IntSyn.exp
    | FailUnify of (IntSyn.head * IntSyn.head) * string

  (* resolved with clause c, fam a *)
  (* clause c, fam a, nth subgoal *)
  (* clause head == goal *)
  (* failure message *)
  val signal : IntSyn.dctx * event -> unit
  val init : unit -> unit

  (* initialize trace, break and tag *)
  val tracing : unit -> bool

  (* currently tracing or using breakpoints *)
  (* User interface *)
  type 'a spec = None | Some of 'a list | All

  val trace : string spec -> unit
  val break : string spec -> unit
  val detail : int ref

  (* 0 = none, 1 = default, 2 = unify *)
  val show : unit -> unit

  (* show trace, break, detail *)
  val reset : unit -> unit
end
