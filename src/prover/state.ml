(* # 1 "src/prover/state.sig.ml" *)
open! Basis

(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)
module type STATE = sig
  exception Error of string

  type state =
    | State of Tomega.worlds * Tomega.dec IntSyn.ctx * Tomega.prg * Tomega.for_
    | StateLF of IntSyn.exp

  type focus = Focus of Tomega.prg * Tomega.worlds | FocusLF of IntSyn.exp

  (* Focus (EVar, W) *)
  (* focus EVar *)
  val init : Tomega.for_ * Tomega.worlds -> state
  val close : state -> bool
  val collectT : Tomega.prg -> Tomega.prg list
  val collectLF : Tomega.prg -> IntSyn.exp list
  val collectLFSub : Tomega.sub -> IntSyn.exp list
end

(* # 1 "src/prover/state.fun.ml" *)
open! Basis

(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)
module State (State__0 : sig
  module Formatter : FORMATTER
end) : STATE = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  module Formatter = Formatter

  type state =
    | State of Tomega.worlds * Tomega.dec IntSyn.ctx * Tomega.prg * Tomega.for_
    | StateLF of IntSyn.exp

  (* StateLF X, X is always lowered *)
  type focus = Focus of Tomega.prg * Tomega.worlds | FocusLF of IntSyn.exp

  (* datatype State
    = State of (Tomega.Dec IntSyn.Ctx * Tomega.For) * Tomega.Worlds
 *)
  (*  datatype SideCondition   we need some work here 
    = None
    | All   of SideCondition
    | And   of SideCondition * SideCondition
    | Order of Order.Predicate
*)
  exception Error of string

  open! struct
    module T = Tomega
    module I = IntSyn

    let rec findPrg = function
      | T.Lam (_, p_) -> findPrg p_
      | T.New p_ -> findPrg p_
      | T.Choose p_ -> findPrg p_
      | T.PairExp (_, p_) -> findPrg p_
      | T.PairBlock (b_, p_) -> findPrg p_
      | T.PairPrg (p1_, p2_) -> findPrg p1_ @ findPrg p2_
      | unit_ -> []
      | T.Rec (_, p_) -> findPrg p_
      | T.Case (T.Cases c_) -> findCases c_
      | T.PClo (p_, t) -> findPrg p_ @ findSub t
      | T.Let (d_, p1_, p2_) -> findPrg p1_ @ findPrg p2_
      | T.LetPairExp (d1_, d2_, p1_, p2_) -> findPrg p1_ @ findPrg p2_
      | T.LetUnit (p1_, p2_) -> findPrg p1_ @ findPrg p2_
      | T.EVar (_, { contents = None }, _, _, _, _) as x_ -> [ x_ ]
      | T.EVar (_, { contents = Some p_ }, _, _, _, _) as x_ -> findPrg p_
      | T.Const _ -> []
      | T.Var _ -> []
      | T.Redex (p_, s_) -> findPrg p_ @ findSpine s_

    and findCases = function
      | [] -> []
      | (_, _, p_) :: c_ -> findPrg p_ @ findCases c_

    and findSub = function
      | T.Shift _ -> []
      | T.Dot (f_, t) -> findFront f_ @ findSub t

    and findFront = function
      | T.Idx _ -> []
      | T.Prg p_ -> findPrg p_
      | T.Exp _ -> []
      | T.Block _ -> []
      | undef_ -> []

    and findSpine = function
      | nil_ -> []
      | T.AppPrg (p_, s_) -> findPrg p_ @ findSpine s_
      | T.AppExp (_, s_) -> findSpine s_
      | T.AppBlock (_, s_) -> findSpine s_

    let rec findExp arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | (psi_, T.Lam (d_, p_)), k_ -> findExp (I.Decl (psi_, d_), p_) k_
      | (psi_, T.New p_), k_ -> findExp (psi_, p_) k_
      | (psi_, T.Choose p_), k_ -> findExp (psi_, p_) k_
      | (psi_, T.PairExp (m_, p_)), k_ ->
          findExp (psi_, p_)
            (Abstract.collectEVars (T.coerceCtx psi_, (m_, I.id), k_))
      | (psi_, T.PairBlock (b_, p_)), k_ -> findExp (psi_, p_) k_
      | (psi_, T.PairPrg (p1_, p2_)), k_ ->
          findExp (psi_, p2_) (findExp (psi_, p1_) k_)
      | (psi_, unit_), k_ -> k_
      | (psi_, T.Rec (d_, p_)), k_ -> findExp (psi_, p_) k_
      | (psi_, T.Case (T.Cases c_)), k_ -> findExpCases (psi_, c_) k_
      | (psi_, T.PClo (p_, t)), k_ ->
          findExpSub (psi_, t) (findExp (psi_, p_) k_)
      | (psi_, T.Let (d_, p1_, p2_)), k_ ->
          findExp (I.Decl (psi_, d_), p2_) (findExp (psi_, p1_) k_)
      | (psi_, T.LetPairExp (d1_, d2_, p1_, p2_)), k_ ->
          findExp
            (I.Decl (I.Decl (psi_, T.UDec d1_), d2_), p2_)
            (findExp (psi_, p1_) k_)
      | (psi_, T.LetUnit (p1_, p2_)), k_ ->
          findExp (psi_, p2_) (findExp (psi_, p1_) k_)
      | (psi_, (T.EVar _ as x_)), k_ -> k_
      | (psi_, T.Const _), k_ -> k_
      | (psi_, T.Var _), k_ -> k_
      | (psi_, T.Redex (p_, s_)), k_ -> findExpSpine (psi_, s_) k_
      end

    and findExpSpine arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | (psi_, nil_), k_ -> k_
      | (psi_, T.AppPrg (_, s_)), k_ -> findExpSpine (psi_, s_) k_
      | (psi_, T.AppExp (m_, s_)), k_ ->
          findExpSpine (psi_, s_)
            (Abstract.collectEVars (T.coerceCtx psi_, (m_, I.id), k_))
      | (psi_, T.AppBlock (_, s_)), k_ -> findExpSpine (psi_, s_) k_
      end

    and findExpCases arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | (psi_, []), k_ -> k_
      | (psi_, (_, _, p_) :: c_), k_ ->
          findExpCases (psi_, c_) (findExp (psi_, p_) k_)
      end

    and findExpSub arg__7 arg__8 =
      begin match (arg__7, arg__8) with
      | (psi_, T.Shift _), k_ -> k_
      | (psi_, T.Dot (f_, t)), k_ ->
          findExpSub (psi_, t) (findExpFront (psi_, f_) k_)
      end

    and findExpFront arg__9 arg__10 =
      begin match (arg__9, arg__10) with
      | (psi_, T.Idx _), k_ -> k_
      | (psi_, T.Prg p_), k_ -> findExp (psi_, p_) k_
      | (psi_, T.Exp m_), k_ ->
          Abstract.collectEVars (T.coerceCtx psi_, (m_, I.id), k_)
      | (psi_, T.Block _), k_ -> k_
      | (psi_, undef_), k_ -> k_
      end

    let rec init (f_, w_) =
      let x_ = T.newEVar (I.Null, f_) in
      State (w_, I.Null, x_, f_)

    let rec close (State (w_, _, p_, _)) =
      begin match (findPrg p_, findExp (I.Null, p_) []) with
      | [], [] -> true
      | _ -> false
      end
  end

  (* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)
  (* by invariant: blocks don't contain free evars *)
  (* find P = [X1 .... Xn]
       Invariant:
       If   P is a well-typed program
       then [X1 .. Xn] are all the open subgoals that occur within P
    *)
  (* by invariant: Blocks don't contain free evars. *)
  (* init F = S

       Invariant:
       S = (. |> F) is the initial state
    *)
  (* close S = B

       Invariant:
       If  B holds iff S  doesn't contain any free subgoals
    *)
  let close = close
  let init = init
  let collectT = findPrg
  let collectLF = function p_ -> findExp (I.Null, p_) []
  let collectLFSub = function s -> findExpSub (I.Null, s) []
end

(* # 1 "src/prover/state.sml.ml" *)
