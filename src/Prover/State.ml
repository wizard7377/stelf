open! Intsyn.Lambda_
open! Formatter.Formatter_

(* # 1 "src/prover/State.sig.ml" *)

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
      | T.Lam (_, p) -> findPrg p
      | T.New p -> findPrg p
      | T.Choose p -> findPrg p
      | T.PairExp (_, p) -> findPrg p
      | T.PairBlock (b, p) -> findPrg p
      | T.PairPrg (p1, p2) -> findPrg p1 @ findPrg p2
      | Unit -> []
      | T.Rec (_, p) -> findPrg p
      | T.Case (T.Cases c) -> findCases c
      | T.PClo (p, t) -> findPrg p @ findSub t
      | T.Let (d, p1, p2) -> findPrg p1 @ findPrg p2
      | T.LetPairExp (d1, d2, p1, p2) -> findPrg p1 @ findPrg p2
      | T.LetUnit (p1, p2) -> findPrg p1 @ findPrg p2
      | T.EVar (_, { contents = None }, _, _, _, _) as x -> [ x ]
      | T.EVar (_, { contents = Some p }, _, _, _, _) as x -> findPrg p
      | T.Const _ -> []
      | T.Var _ -> []
      | T.Redex (p, s) -> findPrg p @ findSpine s

    and findCases = function
      | [] -> []
      | (_, _, p) :: c -> findPrg p @ findCases c

    and findSub = function
      | T.Shift _ -> []
      | T.Dot (f, t) -> findFront f @ findSub t

    and findFront = function
      | T.Idx _ -> []
      | T.Prg p -> findPrg p
      | T.Exp _ -> []
      | T.Block _ -> []
      | T.Undef -> []

    and findSpine = function
      | T.Nil -> []
      | T.AppPrg (p, s) -> findPrg p @ findSpine s
      | T.AppExp (_, s) -> findSpine s
      | T.AppBlock (_, s) -> findSpine s

    let rec findExp arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | (psi, T.Lam (d, p)), k -> findExp (I.Decl (psi, d), p) k
      | (psi, T.New p), k -> findExp (psi, p) k
      | (psi, T.Choose p), k -> findExp (psi, p) k
      | (psi, T.PairExp (m, p)), k ->
          findExp (psi, p)
            (Abstract.collectEVars (T.coerceCtx psi) (m, I.id) k)
      | (psi, T.PairBlock (b, p)), k -> findExp (psi, p) k
      | (psi, T.PairPrg (p1, p2)), k ->
          findExp (psi, p2) (findExp (psi, p1) k)
      | (psi, Unit), k -> k
      | (psi, T.Rec (d, p)), k -> findExp (psi, p) k
      | (psi, T.Case (T.Cases c)), k -> findExpCases (psi, c) k
      | (psi, T.PClo (p, t)), k -> findExpSub (psi, t) (findExp (psi, p) k)
      | (psi, T.Let (d, p1, p2)), k ->
          findExp (I.Decl (psi, d), p2) (findExp (psi, p1) k)
      | (psi, T.LetPairExp (d1, d2, p1, p2)), k ->
          findExp
            (I.Decl (I.Decl (psi, T.UDec d1), d2), p2)
            (findExp (psi, p1) k)
      | (psi, T.LetUnit (p1, p2)), k ->
          findExp (psi, p2) (findExp (psi, p1) k)
      | (psi, (T.EVar _ as x)), k -> k
      | (psi, T.Const _), k -> k
      | (psi, T.Var _), k -> k
      | (psi, T.Redex (p, s)), k -> findExpSpine (psi, s) k
      end

    and findExpSpine arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | (psi, T.Nil), k -> k
      | (psi, T.AppPrg (_, s)), k -> findExpSpine (psi, s) k
      | (psi, T.AppExp (m, s)), k ->
          findExpSpine (psi, s)
            (Abstract.collectEVars (T.coerceCtx psi) (m, I.id) k)
      | (psi, T.AppBlock (_, s)), k -> findExpSpine (psi, s) k
      end

    and findExpCases arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | (psi, []), k -> k
      | (psi, (_, _, p) :: c), k ->
          findExpCases (psi, c) (findExp (psi, p) k)
      end

    and findExpSub arg__7 arg__8 =
      begin match (arg__7, arg__8) with
      | (psi, T.Shift _), k -> k
      | (psi, T.Dot (f, t)), k ->
          findExpSub (psi, t) (findExpFront (psi, f) k)
      end

    and findExpFront arg__9 arg__10 =
      begin match (arg__9, arg__10) with
      | (psi, T.Idx _), k -> k
      | (psi, T.Prg p), k -> findExp (psi, p) k
      | (psi, T.Exp m), k ->
          Abstract.collectEVars (T.coerceCtx psi) (m, I.id) k
      | (psi, T.Block _), k -> k
      | (psi, T.Undef), k -> k
      end

    let init f w =
      let x = T.newEVar I.Null f in
      State (w, I.Null, x, f)

    let close (State (w, _, p, _)) =
      begin match (findPrg p, findExp (I.Null, p) []) with
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
  let collectLF p = findExp (I.Null, p) []
  let collectLFSub s = findExpSub (I.Null, s) []
end

(* # 1 "src/prover/State.sml.ml" *)
