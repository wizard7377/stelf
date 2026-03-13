(* # 1 "src/compile/compSyn.sig.ml" *)
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

(* # 1 "src/compile/compSyn.fun.ml" *)
open! Basis

(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
(* Modified: Brigitte Pientka *)
module Make_CompSyn (CompSyn__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Table : TABLE with type key = int
end) : COMPSYN = struct
  open CompSyn__0

  (*! structure IntSyn = IntSyn' !*)
  type opt_ = No | LinearHeads | Indexing

  let optimize = ref LinearHeads

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
    | In of resGoal_ * IntSyn.exp_ * goal_ (*     | r && (A,g)           *)
    | Exists of IntSyn.dec_ * resGoal_
    | Axists of IntSyn.dec_ * resGoal_

  and auxGoal_ =
    | Trivial
    | UnifyEq of
        IntSyn.dctx * IntSyn.exp_ * IntSyn.exp_ * auxGoal_ (* call unify *)

  (* Goals                      *)
  (* g ::= p                    *)
  (*     | all x:A. g           *)
  (* Residual Goals             *)
  (* r ::= p = ?                *)
  (*     | p = ?, where p has   *)
  (* only new vars,             *)
  (* then unify all the vars    *)
  (*     | exists x:A. r        *)
  (*     | exists' x:_. r       *)
  (* exists' is used for local evars
                                           which are introduced to linearize
                                           the head of a clause;
                                           they do not have a type -bp *)
  (* trivially done *)
  (* Static programs -- compiled version for substitution trees *)
  type conjunction_ = True | Conjunct of goal_ * IntSyn.exp_ * conjunction_

  type compHead_ =
    | Head of IntSyn.exp_ * IntSyn.dec_ IntSyn.ctx_ * auxGoal_ * IntSyn.cid

  (* proof skeletons instead of proof term *)
  type flatterm_ =
    | Pc of IntSyn.cid
    | Dc of IntSyn.cid
    | Csolver of IntSyn.exp_

  type nonrec pskeleton = flatterm_ list

  (* Representation invariants for compiled syntax:
     Judgments:
       G |- g goal   g is a valid goal in G
       G |- r resgoal  g is a valid residual goal in G

       G |- A ~> g   A compiles to goal g
       G |- A ~> r   A compiles to residual goal r
       G |- A ~> <head , subgoals>

     G |- p  goal
     if  G |- p : type, p = H @ S        mod whnf 

     G |- (r, A, a) => g  goal
     if G |- A : type
        G |- r  resgoal
        G |- A ~> r
        a  target head of A (for indexing purposes)

     G |- all x:A. g  goal
     if G |- A : type
        G, x:A |- g  goal

     For dynamic clauses:

     G |- q  resgoal
     if G |- q : type, q = H @ S         mod whnf 

     G |- r & (A,g)  resgoal
     if G |- A : type
        G |- g  goal
        G |- A ~> g
        G, _:A |- r  resgoal

     G |- exists x:A. r  resgoal
     if  G |- A : type
         G, x:A |- r  resgoal

     G |- exists' x:A. r  resgoal     but exists' doesn't effect the proof-term
     if  G |- A : type
         G, x:A |- r  resgoal

     For static clauses:
     G |- true subgoals

     if G |- sg && g subgoals
     if G |- g goal
        G |- sg subgoals

  *)
  (* Static programs --- compiled version of the signature (no indexing) *)
  type conDec_ = SClause of resGoal_ | Void

  (* Compiled constant declaration           *)
  (* c : A  -- static clause (residual goal) *)
  (* Other declarations are ignored          *)
  (* Static programs --- compiled version of the signature (indexed by first argument) *)
  type conDecDirect_ = HeadGoals of compHead_ * conjunction_ | Null

  (* Compiled constant declaration     *)
  (* static clause with direct head access   *)
  (* Other declarations are ignored          *)
  (* Compiled Declarations *)
  (* added Thu Jun 13 13:41:32 EDT 2002 -cs *)
  type comDec_ =
    | Parameter
    | Dec of resGoal_ * IntSyn.sub_ * IntSyn.head_
    | BDec of (resGoal_ * IntSyn.sub_ * IntSyn.head_) list
    | PDec

  (* The dynamic clause pool --- compiled version of the context *)
  (* Dynamic programs: context with synchronous clause pool *)
  type dProg_ = DProg of IntSyn.dctx * comDec_ IntSyn.ctx_

  open! struct
    let maxCid = Global.maxCid
    let sProgArray = (Array.array (maxCid + 1, Void) : conDec_ Array.array)
    let detTable : bool Table.table_ = Table.new_ 32
  end

  (* program array indexed by clause names (no direct head access) *)
  (* Invariants *)
  (* 0 <= cid < I.sgnSize () *)
  (* program array indexed by clause names (no direct head access) *)
  let rec sProgInstall (cid, conDec) = Array.update (sProgArray, cid, conDec)
  let rec sProgLookup cid = Array.sub (sProgArray, cid)
  let rec sProgReset () = Array.modify (function _ -> Void) sProgArray
  let detTableInsert = Table.insert detTable

  let rec detTableCheck cid =
    begin match Table.lookup detTable cid with
    | Some deterministic -> deterministic
    | None -> false
    end

  let rec detTableReset () = Table.clear detTable

  (* goalSub (g, s) = g'

     Invariants:
     If   G  |- s : G'    G' |- g : A
     then g' = g[s]
     and  G  |- g' : A
  *)
  let rec goalSub = function
    | Atom p, s -> Atom (IntSyn.EClo (p, s))
    | Impl (d, a_, ha_, g), s ->
        Impl
          ( resGoalSub (d, s),
            IntSyn.EClo (a_, s),
            ha_,
            goalSub (g, IntSyn.dot1 s) )
    | All (d_, g), s -> All (IntSyn.decSub (d_, s), goalSub (g, IntSyn.dot1 s))

  and resGoalSub = function
    | Eq q, s -> Eq (IntSyn.EClo (q, s))
    | And (r, a_, g), s ->
        And (resGoalSub (r, IntSyn.dot1 s), IntSyn.EClo (a_, s), goalSub (g, s))
    | In (r, a_, g), s ->
        In (resGoalSub (r, IntSyn.dot1 s), IntSyn.EClo (a_, s), goalSub (g, s))
    | Exists (d_, r), s ->
        Exists (IntSyn.decSub (d_, s), resGoalSub (r, IntSyn.dot1 s))

  (* resGoalSub (r, s) = r'

     Invariants:
     If   G  |- s : G'    G' |- r : A
     then r' = r[s]
     and  G  |- r' : A [s]
  *)
  let rec pskeletonToString = function
    | [] -> " "
    | Pc i :: o_ ->
        (Names.qidToString (Names.constQid i) ^ " ") ^ pskeletonToString o_
    | Dc i :: o_ -> (("(Dc " ^ Int.toString i) ^ ") ") ^ pskeletonToString o_
    | Csolver u_ :: o_ -> "(cs _ ) " ^ pskeletonToString o_
end

open Table_instances

(* functor CompSyn *)
module CompSyn = Make_CompSyn (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  module Names = Names
  module Table = IntRedBlackTree
end)

(* # 1 "src/compile/compSyn.sml.ml" *)
