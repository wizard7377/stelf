(* # 1 "src/opsem/table_param.sig.ml" *)
open! Basis
open Red_black_set

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

  type answState = New_ | Repeated_

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
(* signature TABLEPARAM *)

(* # 1 "src/opsem/table_param.fun.ml" *)
open! Basis

(* Table parameters *)
(* Author: Brigitte Pientka *)
module MakeTableParam (TableParam__0 : sig
  module Global : GLOBAL
end) : TABLEPARAM = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  (*! structure RBSet = RBSet !*)
  exception Error of string

  type strategy = Variant | Subsumption

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

  (* globalTable stores the queries whose solution we want to keep *)
  let globalTable :
      (IntSyn.dctx
      * IntSyn.dctx
      * IntSyn.dctx
      * IntSyn.exp
      * resEqn
      * answer
      * status)
      list
      ref =
    ref []

  let rec resetGlobalTable () = globalTable := []
  let rec emptyAnsw () = ref { solutions = []; lookup = 0 }

  let rec addSolution (s_, answRef) =
    let { solutions = sList_; lookup = k } = !answRef in
    answRef := { solutions = s_ :: sList_; lookup = k }

  let rec updateAnswLookup (k', answRef) =
    let { solutions = sList_; lookup = k } = !answRef in
    answRef := { solutions = sList_; lookup = k' }

  let rec solutions ({ contents = { solutions = s_; lookup = i } } as answ) = s_
  let rec lookup ({ contents = { solutions = s_; lookup = i } } as answ) = i

  let rec noAnswers answ =
    begin match List.take (solutions answ, lookup answ) with
    | [] -> true
    | l_ -> false
    end
  (*solutions(answ) *)

  type nonrec asub = IntSyn.exp RBSet.ordSet

  let aid : unit -> asub = RBSet.new_

  type callCheckResult =
    | NewEntry of answer
    | RepeatedEntry of (IntSyn.sub * IntSyn.sub) * answer * status
    | DivergingEntry of IntSyn.sub * answer

  type answState = New_ | Repeated_

  (* ---------------------------------------------------------------------- *)
  (* global search parameters *)
  let strategy = ref Variant

  (* Subsumption *)
  let divHeuristic = ref false

  (*  val divHeuristic = ref true;*)
  let stageCtr = ref 0

  (* term abstraction and ctx abstraction *)
  (* currently not used *)
  let termDepth = (ref None : int option ref)
  let ctxDepth = (ref None : int option ref)
  let ctxLength = (ref None : int option ref)

  (* apply strengthening during abstraction *)
  let strengthen = ref false
end

(*! structure IntSyn' : INTSYN !*)
(*! structure CompSyn' : COMPSYN !*)
(*!  sharing CompSyn'.IntSyn = IntSyn'!*)
(*! structure RBSet : RBSET!*)
(* structure TableParam *)

(* # 1 "src/opsem/table_param.sml.ml" *)
open! Basis

module TableParam = MakeTableParam (struct
  module Global = Global
end)
(*! structure IntSyn' = IntSyn !*)
(*! structure CompSyn' = CompSyn !*)
(*! structure RBSet = RBSet !*)
