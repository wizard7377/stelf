(* # 1 "src/lambda/Tomega.sig.ml" *)
open! Basis
open Intsyn

(* Internal syntax for Delphin *)
(* Author: Carsten Schuermann *)
include Tomega_intf
(* Signature TOMEGA *)

(* # 1 "src/lambda/Tomega.fun.ml" *)
open! Whnf
open! Conv
open! Basis
open Intsyn

(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao, Adam Poswolsky *)
module MakeTomega (Tomega__0 : sig
  module Whnf : WHNF
  module Conv : CONV
end) : TOMEGA = struct
  module Whnf = Tomega__0.Whnf
  module Conv = Tomega__0.Conv

  exception Error of string

  type nonrec label = int
  type nonrec lemma = int
  type worlds = Worlds of IntSyn.cid list
  type quantifier = Implicit | Explicit

  type tC =
    | Abs of IntSyn.dec * tC
    | Conj of tC * tC
    | Base of
        ((IntSyn.exp * IntSyn.sub) * (IntSyn.exp * IntSyn.sub)) Order.order

  (* Terminiation Condition     *)
  (* T ::= {{D}} O              *)
  (*     | O1 ^ O2              *)
  type for_ =
    | World of worlds * for_
    | All of (dec * quantifier) * for_
    | Ex of (IntSyn.dec * quantifier) * for_
    | True
    | And of for_ * for_
    | FClo of for_ * sub
    | FVar of dec IntSyn.ctx * for_ option ref

  and dec =
    | UDec of IntSyn.dec
    | PDec of string option * for_ * tC option * tC option

  and prg =
    | Box of worlds * prg
    | Lam of dec * prg
    | New of prg
    | Choose of prg
    | PairExp of IntSyn.exp * prg
    | PairBlock of IntSyn.block * prg
    | PairPrg of prg * prg
    | Unit
    | Redex of prg * spine
    | Rec of dec * prg
    | Case of cases
    | PClo of prg * sub
    | Let of dec * prg * prg
    | EVar of
        dec IntSyn.ctx
        * prg option ref
        * for_
        * tC option
        * tC option
        * IntSyn.exp
    | Const of lemma
    | Var of int
    | LetPairExp of IntSyn.dec * dec * prg * prg
    | LetUnit of prg * prg

  and spine =
    | Nil
    | AppExp of IntSyn.exp * spine
    | AppBlock of IntSyn.block * spine
    | AppPrg of prg * spine
    | SClo of spine * sub

  and sub = Shift of int | Dot of front * sub

  and front =
    | Idx of int
    | Prg of prg
    | Exp of IntSyn.exp
    | Block of IntSyn.block
    | Undef

  and cases = Cases of (dec IntSyn.ctx * sub * prg) list

  (* Formulas                   *)
  (* F ::= World l1...ln. F     *)
  (*     | All LD. F            *)
  (*     | Ex  D. F             *)
  (*     | T                    *)
  (*     | F1 ^ F2              *)
  (*     | F [t]                *)
  (*     | F (G)                *)
  (* Declaration:               *)
  (* D ::= x:A                  *)
  (*     | xx :: F              *)
  (* Programs:                  *)
  (*     | box W. P             *)
  (*     | lam LD. P            *)
  (*     | new P                *)
  (*     | choose P             *)
  (*     | <M, P>               *)
  (*     | <rho, P>             *)
  (*     | <P1, P2>             *)
  (*     | <>                   *)
  (*     | mu xx. P             *)
  (*     | case t of O          *)
  (*     | P [t]                *)
  (*     | let D = P1 in P2     *)
  (*     | E (G, F, TC)         *)
  (* P ::= cc                   *)
  (*     | xx                   *)
  (* Spines:                    *)
  (* S ::= Nil                  *)
  (*     | P U                  *)
  (*     | P rho                *)
  (*     | P1 P2                *)
  (*     | S [t]                *)
  (* t ::=                      *)
  (*       ^n                   *)
  (*     | F . t                *)
  (* F ::=                      *)
  (*     | i                    *)
  (*     | p                    *)
  (*     | U                    *)
  (*     | _x                   *)
  (*     | _                    *)
  (* Cases                      *)
  (* C ::= (Psi' |> s |-> P)    *)
  type conDec = ForDec of string * for_ | ValDec of string * prg * for_

  (* ConDec                     *)
  (* CD ::= f :: F              *)
  (*      | f == P              *)
  exception NoMatch

  open! struct
    module I = IntSyn
    module O = Order

    let maxLemma = Global.maxCid

    let lemmaArray =
      (Array.array (maxLemma + 1, ForDec ("", True)) : conDec Array.array)

    let nextLemma = ref 0
    let rec lemmaLookup lemma = Array.sub (lemmaArray, lemma)

    let rec lemmaAdd lemmaDec =
      let lemma = !nextLemma in
      begin if lemma > maxLemma then
        raise
          (Error
             (("Global signature size " ^ Int.toString (maxLemma + 1))
             ^ " exceeded"))
      else begin
        Array.update (lemmaArray, lemma, lemmaDec);
        begin
          nextLemma := lemma + 1;
          lemma
        end
      end
      end

    let rec lemmaSize () = !nextLemma

    let rec lemmaDef lemma =
      begin match lemmaLookup lemma with ValDec (_, p_, _) -> p_
      end

    let rec lemmaFor lemma =
      begin match lemmaLookup lemma with
      | ForDec (_, f_) -> f_
      | ValDec (_, _, f_) -> f_
      end

    let rec lemmaName s = lemmaName' !nextLemma s

    and lemmaName' arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | -1, s -> raise (Error "Function name not found")
      | n, s -> begin
          match lemmaLookup n with
          | ForDec (s', f_) -> begin
              if s = s' then n else lemmaName' (n - 1) s
            end
          | ValDec (s', p_, f_) -> begin
              if s = s' then n else lemmaName' (n - 1) s
            end
        end
      end

    let rec coerceFront = function
      | Idx k -> I.Idx k
      | Prg p_ -> I.Undef
      | Exp m_ -> I.Exp m_
      | Block b_ -> I.Block b_
      | Undef -> I.Undef

    let rec embedFront = function
      | I.Idx k -> Idx k
      | I.Exp u_ -> Exp u_
      | I.Block b_ -> Block b_
      | I.Undef -> Undef

    let rec coerceSub = function
      | Shift n -> I.Shift n
      | Dot (ft_, t) -> I.Dot (coerceFront ft_, coerceSub t)

    let rec embedSub = function
      | I.Shift n -> Shift n
      | I.Dot (ft_, s) -> Dot (embedFront ft_, embedSub s)

    let rec revCoerceFront = function
      | I.Idx k -> Idx k
      | I.Exp m_ -> Exp m_
      | I.Block b -> Block b
      | I.Undef -> Undef

    let rec revCoerceSub = function
      | I.Shift n -> Shift n
      | I.Dot (ft_, t) -> Dot (revCoerceFront ft_, revCoerceSub t)

    let rec revCoerceCtx = function
      | I.Null -> I.Null
      | I.Decl (psi_, (I.BDec (_, (l_, t)) as d_)) ->
          I.Decl (revCoerceCtx psi_, UDec d_)

    let id = Shift 0

    let rec dotEta = function
      | (Idx _ as ft_), s -> Dot (ft_, s)
      | (Exp u_ as ft_), s ->
          let ft'_ = try Idx (Whnf.etaContract u_) with eta_ -> ft_ in
          Dot (ft'_, s)
      | (Undef as ft_), s -> Dot (ft_, s)

    let rec embedCtx = function
      | I.Null -> I.Null
      | I.Decl (g_, d_) -> I.Decl (embedCtx g_, UDec d_)

    let rec orderSub = function
      | O.Arg ((u_, s1), (v_, s2)), s ->
          O.Arg ((u_, I.comp (s1, s)), (v_, I.comp (s2, s)))
      | O.Lex os_, s -> O.Lex (map (function o_ -> orderSub (o_, s)) os_)
      | O.Simul os_, s -> O.Simul (map (function o_ -> orderSub (o_, s)) os_)

    let rec tCSub_ = function
      | Base o_, s -> Base (orderSub (o_, s))
      | Conj (tc1_, tc2_), s -> Conj (tCSub_ (tc1_, s), tCSub_ (tc2_, s))
      | Abs (d_, tc_), s -> Abs (I.decSub (d_, s), tCSub_ (tc_, I.dot1 s))

    let rec tCSubOpt_ = function
      | None, s -> None
      | Some tc_, s -> Some (tCSub_ (tc_, s))

    let rec normalizeTC' = function
      | O.Arg (us_, vs_) ->
          O.Arg ((Whnf.normalize us_, I.id), (Whnf.normalize vs_, I.id))
      | O.Lex os_ -> O.Lex (map normalizeTC' os_)
      | O.Simul os_ -> O.Simul (map normalizeTC' os_)

    let rec normalizeTC = function
      | Base o_ -> Base (normalizeTC' o_)
      | Conj (tc1_, tc2_) -> Conj (normalizeTC tc1_, normalizeTC tc2_)
      | Abs (d_, tc_) -> Abs (Whnf.normalizeDec (d_, I.id), normalizeTC tc_)

    let rec normalizeTCOpt = function
      | None -> None
      | Some tc_ -> Some (normalizeTC tc_)

    let rec convTC' = function
      | O.Arg (us1_, _), O.Arg (us2_, _) -> Conv.conv (us1_, us2_)
      | O.Lex os1_, O.Lex os2_ -> convTCs (os1_, os2_)
      | O.Simul os1_, O.Simul os2_ -> convTCs (os1_, os2_)

    and convTCs = function
      | [], [] -> true
      | o1_ :: l1_, o2_ :: l2_ -> convTC' (o1_, o2_) && convTCs (l1_, l2_)

    let rec convTC = function
      | Base o_, Base o'_ -> convTC' (o_, o'_)
      | Conj (tc1_, tc2_), Conj (tc1'_, tc2'_) ->
          convTC (tc1_, tc1'_) && convTC (tc2_, tc2'_)
      | Abs (d_, tc_), Abs (d'_, tc'_) ->
          Conv.convDec ((d_, I.id), (d'_, I.id)) && convTC (tc_, tc'_)
      | _ -> false

    let rec convTCOpt = function
      | None, None -> true
      | Some tc1_, Some tc2_ -> convTC (tc1_, tc2_)
      | _ -> false

    let rec transformTC' = function
      | g_, O.Arg k ->
          let k' = I.ctxLength g_ - k + 1 in
          let (I.Dec (_, v_)) = I.ctxDec (g_, k') in
          O.Arg ((I.Root (I.BVar k', I.Nil), I.id), (v_, I.id))
      | g_, O.Lex os_ ->
          O.Lex (map (function o_ -> transformTC' (g_, o_)) os_)
      | g_, O.Simul os_ ->
          O.Simul (map (function o_ -> transformTC' (g_, o_)) os_)

    let rec transformTC = function
      | g_, All ((UDec d_, _), f_), os_ ->
          Abs (d_, transformTC (I.Decl (g_, d_), f_, os_))
      | g_, And (f1_, f2_), o_ :: os_ ->
          Conj (transformTC (g_, f1_, [ o_ ]), transformTC (g_, f2_, os_))
      | g_, Ex _, o_ :: [] -> Base (transformTC' (g_, o_))

    let rec varSub = function
      | 1, Dot (ft_, t) -> ft_
      | n, Dot (ft_, t) -> varSub (n - 1, t)
      | n, Shift k -> Idx (n + k)

    and frontSub = function
      | Idx n, t -> varSub (n, t)
      | Exp u_, t -> Exp (I.EClo (u_, coerceSub t))
      | Prg p_, t -> Prg (PClo (p_, t))
      | Block b_, t -> Block (I.blockSub (b_, coerceSub t))

    and comp = function
      | Shift 0, t -> t
      | t, Shift 0 -> t
      | Shift n, Dot (ft_, t) -> comp (Shift (n - 1), t)
      | Shift n, Shift m -> Shift (n + m)
      | Dot (ft_, t), t' -> Dot (frontSub (ft_, t'), comp (t, t'))

    let rec dot1 = function
      | Shift 0 as t -> t
      | t -> Dot (Idx 1, comp (t, Shift 1))

    let id = Shift 0
    let shift = Shift 1

    let rec weakenSub = function
      | I.Null -> id
      | I.Decl (psi_, (UDec _ as d_)) -> dot1 (weakenSub psi_)
      | I.Decl (psi_, (PDec _ as d_)) -> comp (weakenSub psi_, shift)

    let rec forSub = function
      | All ((d_, q_), f_), t -> All ((decSub (d_, t), q_), forSub (f_, dot1 t))
      | Ex ((d_, q_), f_), t ->
          Ex ((I.decSub (d_, coerceSub t), q_), forSub (f_, dot1 t))
      | And (f1_, f2_), t -> And (forSub (f1_, t), forSub (f2_, t))
      | FClo (f_, t1), t2 -> forSub (f_, comp (t1, t2))
      | World (w_, f_), t -> World (w_, forSub (f_, t))
      | True, _ -> True

    and decSub = function
      | PDec (x, f_, tc1_, None), t ->
          let s = coerceSub t in
          PDec (x, forSub (f_, t), tCSubOpt_ (tc1_, s), None)
      | UDec d_, t -> UDec (I.decSub (d_, coerceSub t))

    let rec invertSub s =
      let rec getFrontIndex = function
        | Idx k -> Some k
        | Prg p_ -> getPrgIndex p_
        | Exp u_ -> getExpIndex u_
        | Block b_ -> getBlockIndex b_
        | Undef -> None
      and getPrgIndex = function
        | Redex (Var k, Nil) -> Some k
        | Redex (p_, Nil) -> getPrgIndex p_
        | PClo (p_, t) -> begin
            match getPrgIndex p_ with
            | None -> None
            | Some i -> getFrontIndex (varSub (i, t))
          end
        | _ -> None
      and getExpIndex = function
        | I.Root (I.BVar k, I.Nil) -> Some k
        | I.Redex (u_, I.Nil) -> getExpIndex u_
        | I.EClo (u_, t) -> begin
            match getExpIndex u_ with
            | None -> None
            | Some i -> getFrontIndex (revCoerceFront (I.bvarSub (i, t)))
          end
        | I.Lam (I.Dec (_, u1_), u2_) as u_ -> (
            try Some (Whnf.etaContract u_) with eta_ -> None | _ -> None)
      and getBlockIndex = function I.Bidx k -> Some k | _ -> None in
      let rec lookup = function
        | n, Shift _, p -> None
        | n, Dot (Undef, s'), p -> lookup (n + 1, s', p)
        | n, Dot (Idx k, s'), p -> begin
            if k = p then Some n else lookup (n + 1, s', p)
          end
      in
      let rec invertSub'' = function
        | 0, si -> si
        | p, si -> begin
            match lookup (1, s, p) with
            | Some k -> invertSub'' (p - 1, Dot (Idx k, si))
            | None -> invertSub'' (p - 1, Dot (Undef, si))
          end
      in
      let rec invertSub' = function
        | n, Shift p -> invertSub'' (p, Shift n)
        | n, Dot (_, s') -> invertSub' (n + 1, s')
      in
      invertSub' (0, s)

    let rec coerceCtx = function
      | I.Null -> I.Null
      | I.Decl (psi_, UDec d_) -> I.Decl (coerceCtx psi_, d_)
      | I.Decl (psi_, PDec (x, _, _, _)) -> I.Decl (coerceCtx psi_, I.NDec x)

    let rec strengthenCtx psi_ =
      let w = weakenSub psi_ in
      let s = invertSub w in
      (coerceCtx psi_, w, s)

    let rec convFor = function
      | (True, _), (True, _) -> true
      | (All ((d1_, _), f1_), t1), (All ((d2_, _), f2_), t2) ->
          convDec ((d1_, t1), (d2_, t2))
          && convFor ((f1_, dot1 t1), (f2_, dot1 t2))
      | (Ex ((d1_, _), f1_), t1), (Ex ((d2_, _), f2_), t2) ->
          Conv.convDec ((d1_, coerceSub t1), (d2_, coerceSub t2))
          && convFor ((f1_, dot1 t1), (f2_, dot1 t2))
      | (And (f1_, f1'_), t1), (And (f2_, f2'_), t2) ->
          convFor ((f1_, t1), (f2_, t2)) && convFor ((f1'_, t1), (f2'_, t2))
      | _ -> false

    and convDec = function
      | (UDec d1_, t1), (UDec d2_, t2) ->
          Conv.convDec ((d1_, coerceSub t1), (d2_, coerceSub t2))
      | (PDec (_, f1_, tc1_, tc1'_), t1), (PDec (_, f2_, tc2_, tc2'_), t2) ->
        begin
          ignore (convFor ((f1_, t1), (f2_, t2)));
          begin
            ignore (convTCOpt (tc1_, tc1'_));
            convTCOpt (tc2_, tc2'_)
          end
        end

    let rec newEVar (psi_, f_) =
      EVar
        ( psi_,
          ref None,
          f_,
          None,
          None,
          I.newEVar (coerceCtx psi_, I.Uni I.Type) )

    let rec newEVarTC (psi_, f_, tc_, tc'_) =
      EVar
        (psi_, ref None, f_, tc_, tc'_, I.newEVar (coerceCtx psi_, I.Uni I.Type))

    let rec exists = function
      | x, [] -> false
      | x, y :: w2_ -> x = y || exists (x, w2_)

    let rec subset = function
      | [], _ -> true
      | x :: w1_, w2_ -> exists (x, w2_) && subset (w1_, w2_)

    let rec eqWorlds (Worlds w1_, Worlds w2_) =
      subset (w1_, w2_) && subset (w2_, w1_)

    let rec ctxDec (g_, k) =
      let rec ctxDec' = function
        | I.Decl (g'_, UDec (I.Dec (x, v'_))), 1 ->
            UDec (I.Dec (x, I.EClo (v'_, I.Shift k)))
        | I.Decl (g'_, UDec (I.BDec (l, (c, s)))), 1 ->
            UDec (I.BDec (l, (c, I.comp (s, I.Shift k))))
        | I.Decl (g'_, PDec (x, f_, tc1_, tc2_)), 1 ->
            PDec
              ( x,
                forSub (f_, Shift k),
                tCSubOpt_ (tc1_, I.Shift k),
                tCSubOpt_ (tc2_, I.Shift k) )
        | I.Decl (g'_, _), k' -> ctxDec' (g'_, k' - 1)
      in
      ctxDec' (g_, k)

    let rec mkInst = function
      | 0 -> []
      | n -> I.Root (I.BVar n, I.Nil) :: mkInst (n - 1)

    let rec deblockify = function
      | I.Null -> (I.Null, id)
      | I.Decl (g_, I.BDec (x, (c, s))) ->
          let g'_, t' = deblockify g_ in
          let _, l_ = I.constBlock c in
          let n = List.length l_ in
          let g''_ = append (g'_, (l_, I.comp (s, coerceSub t'))) in
          let t'' = comp (t', Shift n) in
          let i_ = I.Inst (mkInst n) in
          let t''' = Dot (Block i_, t'') in
          (g''_, t''')

    and append = function
      | g'_, ([], s) -> g'_
      | g'_, (d_ :: l_, s) ->
          append (I.Decl (g'_, I.decSub (d_, s)), (l_, I.dot1 s))

    let rec whnfFor = function
      | (All (d_, _), t) as ft_ -> ft_
      | (Ex (d_, f_), t) as ft_ -> ft_
      | (And (f1_, f2_), t) as ft_ -> ft_
      | FClo (f_, t1), t2 -> whnfFor (f_, comp (t1, t2))
      | (World (w_, f_), t) as ft_ -> ft_
      | (True, _) as ft_ -> ft_

    let rec normalizePrg = function
      | Var n, t -> begin
          match varSub (n, t) with
          | Prg p_ -> p_
          | Idx _ -> raise Domain
          | Exp _ -> raise Domain
          | Block _ -> raise Domain
          | Undef -> raise Domain
        end
      | PairExp (u_, p'_), t ->
          PairExp (Whnf.normalize (u_, coerceSub t), normalizePrg (p'_, t))
      | PairBlock (b_, p'_), t ->
          PairBlock (I.blockSub (b_, coerceSub t), normalizePrg (p'_, t))
      | PairPrg (p1_, p2_), t ->
          PairPrg (normalizePrg (p1_, t), normalizePrg (p2_, t))
      | Unit, _ -> Unit
      | EVar (_, { contents = Some p_ }, _, _, _, _), t -> PClo (p_, t)
      | (EVar _ as p_), t -> PClo (p_, t)
      | Lam (d_, p_), t -> Lam (normalizeDec (d_, t), normalizePrg (p_, dot1 t))
      | Rec (d_, p_), t -> Rec (normalizeDec (d_, t), normalizePrg (p_, dot1 t))
      | PClo (p_, t), t' -> normalizePrg (p_, comp (t, t'))

    and normalizeSpine = function
      | Nil, t -> Nil
      | AppExp (u_, s_), t ->
          AppExp (Whnf.normalize (u_, coerceSub t), normalizeSpine (s_, t))
      | AppPrg (p_, s_), t ->
          AppPrg (normalizePrg (p_, t), normalizeSpine (s_, t))
      | AppBlock (b_, s_), t ->
          AppBlock (I.blockSub (b_, coerceSub t), normalizeSpine (s_, t))
      | SClo (s_, t1), t2 -> normalizeSpine (s_, comp (t1, t2))

    and normalizeDec = function
      | PDec (name, f_, tc1_, None), t ->
          PDec
            ( name,
              forSub (f_, t),
              normalizeTCOpt (tCSubOpt_ (tc1_, coerceSub t)),
              None )
      | UDec d_, t -> UDec (Whnf.normalizeDec (d_, coerceSub t))

    let rec normalizeSub = function
      | Shift n as s -> s
      | Dot (Prg p_, s) -> Dot (Prg (normalizePrg (p_, id)), normalizeSub s)
      | Dot (Exp e_, s) -> Dot (Exp (Whnf.normalize (e_, I.id)), normalizeSub s)
      | Dot (Block k, s) -> Dot (Block k, normalizeSub s)
      | Dot (Idx k, s) -> Dot (Idx k, normalizeSub s)

    let rec derefPrg = function
      | Var n -> Var n
      | PairExp (u_, p'_) -> PairExp (u_, derefPrg p'_)
      | PairBlock (b_, p'_) -> PairBlock (b_, derefPrg p'_)
      | PairPrg (p1_, p2_) -> PairPrg (derefPrg p1_, derefPrg p2_)
      | Unit -> Unit
      | EVar (_, { contents = Some p_ }, _, _, _, _) -> p_
      | EVar _ as p_ -> p_
      | Lam (d_, p_) -> Lam (derefDec d_, derefPrg p_)
      | Rec (d_, p_) -> Rec (derefDec d_, derefPrg p_)
      | Redex (p_, s_) -> Redex (derefPrg p_, derefSpine s_)
      | Case (Cases cs_) ->
          Case
            (Cases
               (flattenCases
                  (map (function psi_, s, p_ -> (psi_, s, derefPrg p_)) cs_)))
      | Let (d_, p1_, p2_) -> Let (derefDec d_, derefPrg p1_, derefPrg p2_)
      | LetPairExp (d1_, d2_, p1_, p2_) ->
          LetPairExp (d1_, derefDec d2_, derefPrg p1_, derefPrg p2_)
      | LetUnit (p1_, p2_) -> LetUnit (derefPrg p1_, derefPrg p2_)

    and flattenCases = function
      | (psi_, s, Case (Cases l_)) :: cs_ ->
          map
            (function psi'_, s', p'_ -> (psi'_, comp (s, s'), p'_))
            (flattenCases l_)
          @ flattenCases cs_
      | (psi_, s, p_) :: cs_ -> (psi_, s, p_) :: flattenCases cs_
      | [] -> []

    and derefSpine = function
      | Nil -> Nil
      | AppExp (u_, s_) -> AppExp (u_, derefSpine s_)
      | AppPrg (p_, s_) -> AppPrg (derefPrg p_, derefSpine s_)
      | AppBlock (b_, s_) -> AppBlock (b_, derefSpine s_)

    and derefDec = function
      | PDec (name, f_, tc1_, tc2_) -> PDec (name, f_, tc1_, tc2_)
      | UDec d_ -> UDec d_
  end

  (* not very efficient, improve !!! *)
  (* coerceFront F = F'

       Invariant:
       If    Psi |- F front
       and   G = mu G. G \in Psi
       then  G   |- F' front
    *)
  (* --Yu Liao Why cases: Block, Undef aren't defined *)
  (* embedFront F = F'

       Invariant:
       If    Psi |- F front
       and   G = mu G. G \in Psi
       then  G   |- F' front
    *)
  (* coerceSub t = s

       Invariant:
       If    Psi |- t : Psi'
       then  G   |- s : G'
       where G = mu G. G \in Psi
       and   G' = mu G. G \in Psi'
    *)
  (* Definition:
       |- Psi ctx[block] holds iff Psi = _x_1 : (L1, t1), ... _x_n : (Ln, tn)
    *)
  (* revCoerceSub t = s
    coerce substitution in LF level t ==> s in Tomega level *)
  (* Invariant Yu? *)
  (* dotEta (Ft, s) = s'

       Invariant:
       If   G |- s : G1, V  and G |- Ft : V [s]
       then Ft  =eta*=>  Ft1
       and  s' = Ft1 . s
       and  G |- s' : G1, V
    *)
  (* embedCtx G = Psi

       Invariant:
       If   G is an LF ctx
       then Psi is G, embedded into Tomega
    *)
  (* orderSub (O, s) = O'

         Invariant:
         If   G' |- O order    and    G |- s : G'
         then G |- O' order
         and  G |- O' == O[s] order
      *)
  (* normalizeTC (O) = O'

         Invariant:
         If   G |- O TC
         then G |- O' TC
         and  G |- O = O' TC
         and  each sub term of O' is in normal form.
      *)
  (* convTC (O1, O2) = B'

         Invariant:
         If   G |- O1 TC
         and  G |- O2 TC
         then B' holds iff G |- O1 == O2 TC
      *)
  (* bvarSub (n, t) = Ft'

       Invariant:
       If    Psi |- t : Psi'    Psi' |- n :: F
       then  Ft' = Ftn          if  t = Ft1 .. Ftn .. ^k
         or  Ft' = ^(n+k)       if  t = Ft1 .. Ftm ^k   and m<n
       and   Psi |- Ft' :: F [t]
    *)
  (* frontSub (Ft, t) = Ft'

       Invariant:
       If   Psi |- Ft :: F
       and  Psi' |- t :: Psi
       then Ft' = Ft[t]
       and  Psi' |- Ft' :: F[t]
    *)
  (* Block case is missing --cs *)
  (* comp (t1, t2) = t

       Invariant:
       If   Psi'' |- t2 :: Psi'
       and  Psi' |- t1 :: Psi
       then t = t1 o t2
       and  Psi'' |- t1 o t2 :: Psi'
    *)
  (* dot1 (t) = t'

       Invariant:
       If   G |- t : G'
       then t' = 1. (t o ^)
       and  for all V t.t.  G' |- V : L
            G, V[t] |- t' : G', V

       If t patsub then t' patsub
    *)
  (* weakenSub (Psi) = w

       Invariant:
       If   Psi is a context
       then G is embed Psi
       and  Psi |- w : G
    *)
  (* forSub (F, t) = F'

       Invariant:
       If    Psi |- F for
       and   Psi' |- t : Psi
       then  Psi' |- F' = F[t] for
    *)
  (* decSub (x::F, t) = D'

       Invariant:
       If   Psi  |- t : Psi'    Psi' |- F formula
       then D' = x:F[t]
       and  Psi  |- F[t] formula
    *)
  (* invertSub s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id
    *)
  (* returns NONE if not found *)
  (* getPrgIndex returns NONE if it is not an index *)
  (* it is possible in the matchSub that we will get PClo under a sub (usually id) *)
  (* getExpIndex returns NONE if it is not an index *)
  (* getBlockIndex returns NONE if it is not an index *)
  (* Suggested by ABP
         * If you do not want this, remove the getFrontIndex and other
          | lookup (n, Dot (Ft, s'), p) =
              (case getFrontIndex(Ft) of
                 NONE => lookup (n+1, s', p)
               | SOME k => if (k=p) then SOME n else lookup (n+1, s', p))
        *)
  (* coerceCtx (Psi) = G

       Invariant:
       If   |- Psi ctx[block]
       then |- G lf-ctx[block]
       and  |- Psi == G
    *)
  (* coerceCtx (Psi) = (G, s)

       Invariant:
       If   |- Psi ctx[block]
       then |- G lf-ctx[block]
       and  |- Psi == G
       and  G |- s : Psi
    *)
  (* convFor ((F1, t1), (F2, t2)) = B

       Invariant:
       If   G |- t1 : G1
       and  G1 |- F1 : formula
       and  G |- t2 : G2
       and  G2 |- F2 : formula
       and  (F1, F2 do not contain abstraction over contextblocks )
       then B holds iff G |- F1[s1] = F2[s2] formula
    *)
  (* newEVar (G, V) = newEVarCnstr (G, V, nil) *)
  (* ctxDec (G, k) = x:V
     Invariant:
     If      |G| >= k, where |G| is size of G,
     then    G |- k : V  and  G |- V : L
  *)
  (* ctxDec' (G'', k') = x:V
             where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
  (* ctxDec' (I.Null, k')  should not occur by invariant *)
  (* mkInst (n) = iota

        Invariant:
        iota = n.n-1....1
     *)
  (* deblockify G = (G', t')

       Invariant:
       If   |- G ctx
       then G' |- t' : G
    *)
  (* G' |- t' : G *)
  (* G'' = G', V1 ... Vn *)
  (* G'' |- t'' : G *)
  (* I = (n, n-1 ... 1)  *)
  (* G'' |- t''' : G, x:(c,s) *)
  (* whnfFor (F, t) = (F', t')

       Invariant:
       If    Psi |- F for
       and   Psi' |- t : Psi
       then  Psi' |- t' : Psi''
       and   Psi'' |- F' :for
       and   Psi' |- F'[t'] = F[t] for
    *)
  (* normalizePrg (P, t) = (P', t')

       Invariant:
       If   Psi' |- V :: F
       and  Psi' |- V value
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F'
       s.t. Psi'' |- F' for
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *)
  (* derefPrg (P, t) = (P', t')

       Invariant:
       If   Psi' |- V :: F
       and  Psi' |- V value
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F'
       s.t. Psi'' |- F' for
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *)
  let lemmaLookup = lemmaLookup
  let lemmaAdd = lemmaAdd
  let lemmaSize = lemmaSize
  let lemmaDef = lemmaDef
  let lemmaName = lemmaName
  let lemmaFor = lemmaFor
  let coerceSub = coerceSub
  let coerceCtx = coerceCtx
  let strengthenCtx = strengthenCtx
  let embedCtx = embedCtx
  let id = id
  let shift = shift
  let comp = comp
  let dot1 = dot1
  let varSub = varSub
  let decSub = decSub
  let weakenSub = weakenSub
  let invertSub = invertSub
  let ctxDec = ctxDec
  let forSub = forSub
  let whnfFor = whnfFor
  let normalizePrg = normalizePrg
  let normalizeSub = normalizeSub
  let derefPrg = derefPrg
  let id = id
  let dotEta = dotEta
  let convFor = convFor
  let newEVar = newEVar
  let newEVarTC = newEVarTC

  (* Below are added by Yu Liao *)
  let embedSub = embedSub
  let eqWorlds = eqWorlds
  let ctxDec = ctxDec
  let revCoerceSub = revCoerceSub
  let revCoerceCtx = revCoerceCtx

  (* Added referenced by ABP *)
  let coerceFront = coerceFront
  let revCoerceFront = revCoerceFront
  let deblockify = deblockify

  (* Stuff that has to do with termination conditions *)
  let tCSub = tCSub_
  let normalizeTC = normalizeTC
  let convTC = convTC
  let transformTC = transformTC
end
(* functor FunSyn *)

(* # 1 "src/lambda/Tomega.sml.ml" *)
open! Basis
module Whnf__ = Whnf ()

module Conv__ = Conv (struct
  module Whnf = Whnf__
end)

module Tomega : TOMEGA = MakeTomega (struct
  module Whnf = Whnf__
  module Conv = Conv__
end)

include Tomega
