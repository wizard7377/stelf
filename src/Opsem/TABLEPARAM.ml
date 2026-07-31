open! Basis
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Formatter
open! Formatter__Formatter_
open! Index
open! Index.Index_
open! Typecheck
open! Typecheck.Typecheck_
open! Solvers
open! Solvers.Solvers_
open! Subordinate
open! Subordinate
open! Compile
open! Compile.Compile_
open! CompSyn
open! Assign
open! Tabling

(* # 1 "src/opsem/TableParam.sig.ml" *)
open! Basis
open RedBlackSet

(* Global Table parameters *)
(* Author: Brigitte Pientka *)

module type TABLEPARAM = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  (*! structure RBSet : RBSET !*)
  exception Error of string

  (* Residual equation *)
  type resEqn =
    | Trivial
    | Unify of IntSyn.dctx * IntSyn.exp * IntSyn.exp * resEqn (* call unify *)

  (* trivially done *)
  type nonrec __0 = {
    solutions : ((IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton) list;
    lookup : int;
  }

  type nonrec answer = __0 ref
  type status = Complete | Incomplete

  val globalTable :
    (IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.exp
    * resEqn
    * answer
    * status)
    list
    ref

  val resetGlobalTable : unit -> unit
  val emptyAnsw : unit -> answer

  (* destructively updates answers *)
  val addSolution :
    ((IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton) * answer -> unit

  val updateAnswLookup : int * answer -> unit

  val solutions :
    answer -> ((IntSyn.dctx * IntSyn.sub) * CompSyn.pskeleton) list

  val lookup : answer -> int
  val noAnswers : answer -> bool

  (* ---------------------------------------------------------------------- *)
  type nonrec asub = IntSyn.exp RBSet.ordSet

  val aid : unit -> asub

  type callCheckResult =
    | NewEntry of answer
    | RepeatedEntry of (IntSyn.sub * IntSyn.sub) * answer * status
    | DivergingEntry of IntSyn.sub * answer

  type answState = New_ | Repeated

  (* ---------------------------------------------------------------------- *)
  type strategy = Variant | Subsumption

  val strategy : strategy ref
  val stageCtr : int ref
  val divHeuristic : bool ref
  val termDepth : int option ref
  val ctxDepth : int option ref
  val ctxLength : int option ref
  val strengthen : bool ref
end
