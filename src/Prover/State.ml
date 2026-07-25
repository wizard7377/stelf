(* # 1 "src/prover/State.sig.ml" *)
open! Basis

(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)
include STATE

(* # 1 "src/prover/State.fun.ml" *)
open! Basis

(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

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
  exception Error = Error

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
      | Unit -> []
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
      | T.Undef -> []

    and findSpine = function
      | T.Nil -> []
      | T.AppPrg (p_, s_) -> findPrg p_ @ findSpine s_
      | T.AppExp (_, s_) -> findSpine s_
      | T.AppBlock (_, s_) -> findSpine s_

    let rec findExp arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | (psi, T.Lam (d_, p_)), k_ -> findExp (I.Decl (psi, d_), p_) k_
      | (psi, T.New p_), k_ -> findExp (psi, p_) k_
      | (psi, T.Choose p_), k_ -> findExp (psi, p_) k_
      | (psi, T.PairExp (m_, p_)), k_ ->
          findExp (psi, p_)
            (Abstract.collectEVars (T.coerceCtx psi, (m_, I.id), k_))
      | (psi, T.PairBlock (b_, p_)), k_ -> findExp (psi, p_) k_
      | (psi, T.PairPrg (p1_, p2_)), k_ ->
          findExp (psi, p2_) (findExp (psi, p1_) k_)
      | (psi, Unit), k_ -> k_
      | (psi, T.Rec (d_, p_)), k_ -> findExp (psi, p_) k_
      | (psi, T.Case (T.Cases c_)), k_ -> findExpCases (psi, c_) k_
      | (psi, T.PClo (p_, t)), k_ -> findExpSub (psi, t) (findExp (psi, p_) k_)
      | (psi, T.Let (d_, p1_, p2_)), k_ ->
          findExp (I.Decl (psi, d_), p2_) (findExp (psi, p1_) k_)
      | (psi, T.LetPairExp (d1_, d2_, p1_, p2_)), k_ ->
          findExp
            (I.Decl (I.Decl (psi, T.UDec d1_), d2_), p2_)
            (findExp (psi, p1_) k_)
      | (psi, T.LetUnit (p1_, p2_)), k_ ->
          findExp (psi, p2_) (findExp (psi, p1_) k_)
      | (psi, (T.EVar _ as x_)), k_ -> k_
      | (psi, T.Const _), k_ -> k_
      | (psi, T.Var _), k_ -> k_
      | (psi, T.Redex (p_, s_)), k_ -> findExpSpine (psi, s_) k_
      end

    and findExpSpine arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | (psi, T.Nil), k_ -> k_
      | (psi, T.AppPrg (_, s_)), k_ -> findExpSpine (psi, s_) k_
      | (psi, T.AppExp (m_, s_)), k_ ->
          findExpSpine (psi, s_)
            (Abstract.collectEVars (T.coerceCtx psi, (m_, I.id), k_))
      | (psi, T.AppBlock (_, s_)), k_ -> findExpSpine (psi, s_) k_
      end

    and findExpCases arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | (psi, []), k_ -> k_
      | (psi, (_, _, p_) :: c_), k_ ->
          findExpCases (psi, c_) (findExp (psi, p_) k_)
      end

    and findExpSub arg__7 arg__8 =
      begin match (arg__7, arg__8) with
      | (psi, T.Shift _), k_ -> k_
      | (psi, T.Dot (f_, t)), k_ ->
          findExpSub (psi, t) (findExpFront (psi, f_) k_)
      end

    and findExpFront arg__9 arg__10 =
      begin match (arg__9, arg__10) with
      | (psi, T.Idx _), k_ -> k_
      | (psi, T.Prg p_), k_ -> findExp (psi, p_) k_
      | (psi, T.Exp m_), k_ ->
          Abstract.collectEVars (T.coerceCtx psi, (m_, I.id), k_)
      | (psi, T.Block _), k_ -> k_
      | (psi, T.Undef), k_ -> k_
      end

    let init (f_, w_) =
      let x_ = T.newEVar (I.Null, f_) in
      State (w_, I.Null, x_, f_)

    let close (State (w_, _, p_, _)) =
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
  let collectLF p_ = findExp (I.Null, p_) []
  let collectLFSub s = findExpSub (I.Null, s) []
end

(* # 1 "src/prover/State.sml.ml" *)
