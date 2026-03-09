open! Basis

(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
module type COMPSYN = sig
  (*! structure IntSyn : INTSYN !*)
  type opt_ = No | LinearHeads | Indexing

  val optimize : opt_ ref

  type goal_ =
    | Atom of IntSyn.exp_
    | Impl of
        resGoal_
        * IntSyn.exp_
        * IntSyn.head_
        * goal_ (*     | (r,A,a) => g         *)
    | All of IntSyn.dec_ * goal_

  and resGoal_ =
    | Eq of IntSyn.exp_
    | Assign of IntSyn.exp_ * auxGoal_
    | And of resGoal_ * IntSyn.exp_ * goal_ (*     | r & (A,g)            *)
    | In of resGoal_ * IntSyn.exp_ * goal_ (*     | r virt& (A,g)        *)
    | Exists of IntSyn.dec_ * resGoal_
    | Axists of IntSyn.dec_ * resGoal_

  and auxGoal_ =
    | Trivial
    | UnifyEq of
        IntSyn.dctx * IntSyn.exp_ * IntSyn.exp_ * auxGoal_ (* call unify *)

  (* Goals                      *)
  (* g ::= p                    *)
  (*     | all x:A. g           *)
  (* dynamic clauses *)
  (* Residual Goals             *)
  (* r ::= p = ?                *)
  (*     | p = ?, where p has   *)
  (* only new vars,             *)
  (* then unify all the vars    *)
  (*     | exists x:A. r        *)
  (*     | exists x:_. r        *)
  (* trivially done *)
  (* Static programs -- compiled version for substitution trees *)
  type conjunction_ = True | Conjunct of goal_ * IntSyn.exp_ * conjunction_

  type compHead_ =
    | Head of IntSyn.exp_ * IntSyn.dec_ IntSyn.ctx_ * auxGoal_ * IntSyn.cid

  (* pskeleton instead of proof term *)
  type flatterm_ = Pc of int | Dc of int | Csolver of IntSyn.exp_
  type nonrec pskeleton = flatterm_ list

  (* The dynamic clause pool --- compiled version of the context *)
  (* type dpool = (ResGoal * IntSyn.Sub * IntSyn.cid) option IntSyn.Ctx *)
  (* Compiled Declarations *)
  (* added Thu Jun 13 13:41:32 EDT 2002 -cs *)
  type comDec_ =
    | Parameter
    | Dec of resGoal_ * IntSyn.sub_ * IntSyn.head_
    | BDec of (resGoal_ * IntSyn.sub_ * IntSyn.head_) list
    | PDec

  (* Dynamic programs: context with synchronous clause pool *)
  type dProg_ = DProg of IntSyn.dctx * comDec_ IntSyn.ctx_

  (* Programs --- compiled version of the signature (no direct head access) *)
  type conDec_ = SClause of resGoal_ | Void

  (* Compiled constant declaration *)
  (* c : A  -- static clause (residual goal) *)
  (* Other declarations are ignored  *)
  (* Install Programs (without indexing) *)
  val sProgInstall : IntSyn.cid * conDec_ -> unit
  val sProgLookup : IntSyn.cid -> conDec_
  val sProgReset : unit -> unit

  (* Deterministic flag *)
  val detTableInsert : IntSyn.cid * bool -> unit
  val detTableCheck : IntSyn.cid -> bool
  val detTableReset : unit -> unit

  (* Explicit Substitutions *)
  val goalSub : goal_ * IntSyn.sub_ -> goal_
  val resGoalSub : resGoal_ * IntSyn.sub_ -> resGoal_
  val pskeletonToString : pskeleton -> string
end
(* signature COMPSYN *)
