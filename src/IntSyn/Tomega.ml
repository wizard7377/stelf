open! Global.Global_

(* # 1 "src/lambda/Tomega.sig.ml" *)
open Intsyn_

(* Internal syntax for Delphin *)
(* Author: Carsten Schuermann *)
include TOMEGA
(* Signature TOMEGA *)

(* # 1 "src/lambda/Tomega.fun.ml" *)
open! Whnf
open! Conv
open! Basis
open Intsyn_

(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao, Adam Poswolsky *)
module MakeTomega (Whnf : WHNF) (Conv : CONV) : TOMEGA = struct
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
    let lemmaLookup lemma = Array.sub (lemmaArray, lemma)

    let lemmaAdd lemmaDec =
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

    let lemmaSize () = !nextLemma

    let lemmaDef lemma =
      begin match lemmaLookup lemma with ValDec (_, p, _) -> p
      end

    let lemmaFor lemma =
      begin match lemmaLookup lemma with
      | ForDec (_, f) -> f
      | ValDec (_, _, f) -> f
      end

    let rec lemmaName s = lemmaName' !nextLemma s

    and lemmaName' arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | -1, s -> raise (Error "Function name not found")
      | n, s ->
          begin match lemmaLookup n with
          | ForDec (s', f) ->
              begin if s = s' then n else lemmaName' (n - 1) s
              end
          | ValDec (s', p, f) ->
              begin if s = s' then n else lemmaName' (n - 1) s
              end
          end
      end

    let coerceFront = function
      | Idx k -> I.Idx k
      | Prg p -> I.Undef
      | Exp m -> I.Exp m
      | Block b -> I.Block b
      | Undef -> I.Undef

    let embedFront = function
      | I.Idx k -> Idx k
      | I.Exp u -> Exp u
      | I.Block b -> Block b
      | I.Undef -> Undef

    let rec coerceSub = function
      | Shift n -> I.Shift n
      | Dot (ft, t) -> I.Dot (coerceFront ft, coerceSub t)

    let rec embedSub = function
      | I.Shift n -> Shift n
      | I.Dot (ft, s) -> Dot (embedFront ft, embedSub s)

    let revCoerceFront = function
      | I.Idx k -> Idx k
      | I.Exp m -> Exp m
      | I.Block b -> Block b
      | I.Undef -> Undef

    let rec revCoerceSub = function
      | I.Shift n -> Shift n
      | I.Dot (ft, t) -> Dot (revCoerceFront ft, revCoerceSub t)

    let rec revCoerceCtx = function
      | I.Null -> I.Null
      | I.Decl (psi, (I.BDec (_, (l, t)) as d)) ->
          I.Decl (revCoerceCtx psi, UDec d)

    let id = Shift 0

    let dotEta a1 b1 = match a1, b1 with
      | (Idx _ as ft), s -> Dot (ft, s)
      | (Exp u as ft), s ->
          let ft' = try Idx (Whnf.etaContract u) with eta -> ft in
          Dot (ft', s)
      | (Undef as ft), s -> Dot (ft, s)

    let rec embedCtx = function
      | I.Null -> I.Null
      | I.Decl (g, d) -> I.Decl (embedCtx g, UDec d)

    let rec orderSub a1 b1 = match a1, b1 with
      | O.Arg ((u, s1), (v, s2)), s ->
          O.Arg ((u, I.comp s1 s), (v, I.comp s2 s))
      | O.Lex os, s -> O.Lex (map (function o -> orderSub o s) os)
      | O.Simul os, s -> O.Simul (map (function o -> orderSub o s) os)

    let rec tCSub_ (a, s) = match a with
      | Base o -> Base (orderSub o s)
      | Conj (tc1, tc2) -> Conj (tCSub_ (tc1, s), tCSub_ (tc2, s))
      | Abs (d, tc) -> Abs (I.decSub d s, tCSub_ (tc, I.dot1 s))

    let tCSubOpt (a, s) = match a with
      | None -> None
      | Some tc -> Some (tCSub_ (tc, s))

    let rec normalizeTC' = function
      | O.Arg (us, vs) ->
          O.Arg ((Whnf.normalize us, I.id), (Whnf.normalize vs, I.id))
      | O.Lex os -> O.Lex (map normalizeTC' os)
      | O.Simul os -> O.Simul (map normalizeTC' os)

    let rec normalizeTC = function
      | Base o -> Base (normalizeTC' o)
      | Conj (tc1, tc2) -> Conj (normalizeTC tc1, normalizeTC tc2)
      | Abs (d, tc) -> Abs (Whnf.normalizeDec d I.id, normalizeTC tc)

    let normalizeTCOpt = function
      | None -> None
      | Some tc -> Some (normalizeTC tc)

    let rec convTC' = function
      | O.Arg (us1, _), O.Arg (us2, _) -> Conv.conv us1 us2
      | O.Lex os1, O.Lex os2 -> convTCs (os1, os2)
      | O.Simul os1, O.Simul os2 -> convTCs (os1, os2)

    and convTCs = function
      | [], [] -> true
      | o1 :: l1, o2 :: l2 -> convTC' (o1, o2) && convTCs (l1, l2)

    let rec convTC a1 b1 = match a1, b1 with
      | Base o, Base o' -> convTC' (o, o')
      | Conj (tc1, tc2), Conj (tc1', tc2') ->
          convTC tc1 tc1' && convTC tc2 tc2'
      | Abs (d, tc), Abs (d', tc') ->
          Conv.convDec d I.id (d', I.id) && convTC tc tc'
      | _ -> false

    let convTCOpt = function
      | None, None -> true
      | Some tc1, Some tc2 -> convTC tc1 tc2
      | _ -> false

    let rec transformTC' (g, a) = match a with
      | O.Arg k ->
          let k' = I.ctxLength g - k + 1 in
          let (I.Dec (_, v)) = I.ctxDec g k' in
          O.Arg ((I.Root (I.BVar k', I.Nil), I.id), (v, I.id))
      | O.Lex os ->
          O.Lex (map (function o -> transformTC' (g, o)) os)
      | O.Simul os ->
          O.Simul (map (function o -> transformTC' (g, o)) os)

    let rec transformTC a1 b1 c1 = match a1, b1, c1 with
      | g, All ((UDec d, _), f), os ->
          Abs (d, transformTC (I.Decl (g, d)) f os)
      | g, And (f1, f2), o :: os ->
          Conj (transformTC g f1 [ o ], transformTC g f2 os)
      | g, Ex _, o :: [] -> Base (transformTC' (g, o))

    let rec varSub a1 b1 = match a1, b1 with
      | 1, Dot (ft, t) -> ft
      | n, Dot (ft, t) -> varSub (n - 1) t
      | n, Shift k -> Idx (n + k)

    and frontSub a1 b1 = match a1, b1 with
      | Idx n, t -> varSub n t
      | Exp u, t -> Exp (I.EClo (u, coerceSub t))
      | Prg p, t -> Prg (PClo (p, t))
      | Block b, t -> Block (I.blockSub b (coerceSub t))

    and comp a1 b1 = match a1, b1 with
      | Shift 0, t -> t
      | t, Shift 0 -> t
      | Shift n, Dot (ft, t) -> comp (Shift (n - 1)) t
      | Shift n, Shift m -> Shift (n + m)
      | Dot (ft, t), t' -> Dot (frontSub ft t', comp t t')

    let dot1 = function Shift 0 as t -> t | t -> Dot (Idx 1, comp t (Shift 1))
    let id = Shift 0
    let shift = Shift 1

    let rec weakenSub = function
      | I.Null -> id
      | I.Decl (psi, (UDec _ as d)) -> dot1 (weakenSub psi)
      | I.Decl (psi, (PDec _ as d)) -> comp (weakenSub psi) shift

    let rec forSub a1 b1 = match a1, b1 with
      | All ((d, q), f), t -> All ((decSub d t, q), forSub f (dot1 t))
      | Ex ((d, q), f), t ->
          Ex ((I.decSub d (coerceSub t), q), forSub f (dot1 t))
      | And (f1, f2), t -> And (forSub f1 t, forSub f2 t)
      | FClo (f, t1), t2 -> forSub f (comp t1 t2)
      | World (w, f), t -> World (w, forSub f t)
      | True, _ -> True

    and decSub a1 b1 = match a1, b1 with
      | PDec (x, f, tc1, None), t ->
          let s = coerceSub t in
          PDec (x, forSub f t, tCSubOpt (tc1, s), None)
      | UDec d, t -> UDec (I.decSub d (coerceSub t))

    let invertSub s =
      let rec getFrontIndex = function
        | Idx k -> Some k
        | Prg p -> getPrgIndex p
        | Exp u -> getExpIndex u
        | Block b -> getBlockIndex b
        | Undef -> None
      and getPrgIndex = function
        | Redex (Var k, Nil) -> Some k
        | Redex (p, Nil) -> getPrgIndex p
        | PClo (p, t) ->
            begin match getPrgIndex p with
            | None -> None
            | Some i -> getFrontIndex (varSub i t)
            end
        | _ -> None
      and getExpIndex = function
        | I.Root (I.BVar k, I.Nil) -> Some k
        | I.Redex (u, I.Nil) -> getExpIndex u
        | I.EClo (u, t) ->
            begin match getExpIndex u with
            | None -> None
            | Some i -> getFrontIndex (revCoerceFront (I.bvarSub i t))
            end
        | I.Lam (I.Dec (_, u1), u2) as u -> (
            try Some (Whnf.etaContract u) with eta -> None | _ -> None)
      and getBlockIndex = function I.Bidx k -> Some k | _ -> None in
      let rec lookup (n, a, p) = match a with
        | Shift _ -> None
        | Dot (Undef, s') -> lookup (n + 1, s', p)
        | Dot (Idx k, s') ->
            begin if k = p then Some n else lookup (n + 1, s', p)
            end
      in
      let rec invertSub'' (p, si) = match p with
        | 0 -> si
        | p ->
            begin match lookup (1, s, p) with
            | Some k -> invertSub'' (p - 1, Dot (Idx k, si))
            | None -> invertSub'' (p - 1, Dot (Undef, si))
            end
      in
      let rec invertSub' (n, a) = match a with
        | Shift p -> invertSub'' (p, Shift n)
        | Dot (_, s') -> invertSub' (n + 1, s')
      in
      invertSub' (0, s)

    let rec coerceCtx = function
      | I.Null -> I.Null
      | I.Decl (psi, UDec d) -> I.Decl (coerceCtx psi, d)
      | I.Decl (psi, PDec (x, _, _, _)) -> I.Decl (coerceCtx psi, I.NDec x)

    let strengthenCtx psi =
      let w = weakenSub psi in
      let s = invertSub w in
      (coerceCtx psi, w, s)

    let rec convFor a1 a2 b1 = match (a1, a2), b1 with
      | (True, _), (True, _) -> true
      | (All ((d1, _), f1), t1), (All ((d2, _), f2), t2) ->
          convDec d1 t1 (d2, t2)
          && convFor f1 (dot1 t1) (f2, dot1 t2)
      | (Ex ((d1, _), f1), t1), (Ex ((d2, _), f2), t2) ->
          Conv.convDec d1 (coerceSub t1) (d2, coerceSub t2)
          && convFor f1 (dot1 t1) (f2, dot1 t2)
      | (And (f1, f1'), t1), (And (f2, f2'), t2) ->
          convFor f1 t1 (f2, t2) && convFor f1' t1 (f2', t2)
      | _ -> false

    and convDec a1 a2 b1 = match (a1, a2), b1 with
      | (UDec d1, t1), (UDec d2, t2) ->
          Conv.convDec d1 (coerceSub t1) (d2, coerceSub t2)
      | (PDec (_, f1, tc1, tc1'), t1), (PDec (_, f2, tc2, tc2'), t2) -> begin
          ignore (convFor f1 t1 (f2, t2));
          begin
            ignore (convTCOpt (tc1, tc1'));
            convTCOpt (tc2, tc2')
          end
        end

    let newEVar psi f =
      EVar
        (psi, ref None, f, None, None, I.newEVar (coerceCtx psi) (I.Uni I.Type))

    let newEVarTC (psi, f, tc, tc') =
      EVar (psi, ref None, f, tc, tc', I.newEVar (coerceCtx psi) (I.Uni I.Type))

    let rec exists a1 b1 = match a1, b1 with
      | x, [] -> false
      | x, y :: w2 -> x = y || exists x w2

    let rec subset (a, w2) = match a with
      | [] -> true
      | x :: w1 -> exists x w2 && subset (w1, w2)

    let eqWorlds (Worlds w1) (Worlds w2) =
      subset (w1, w2) && subset (w2, w1)

    let ctxDec g k =
      let rec ctxDec' = function
        | I.Decl (g', UDec (I.Dec (x, v'))), 1 ->
            UDec (I.Dec (x, I.EClo (v', I.Shift k)))
        | I.Decl (g', UDec (I.BDec (l, (c, s)))), 1 ->
            UDec (I.BDec (l, (c, I.comp s (I.Shift k))))
        | I.Decl (g', PDec (x, f, tc1, tc2)), 1 ->
            PDec
              ( x,
                forSub f (Shift k),
                tCSubOpt (tc1, I.Shift k),
                tCSubOpt (tc2, I.Shift k) )
        | I.Decl (g', _), k' -> ctxDec' (g', k' - 1)
      in
      ctxDec' (g, k)

    let rec mkInst = function
      | 0 -> []
      | n -> I.Root (I.BVar n, I.Nil) :: mkInst (n - 1)

    let rec deblockify = function
      | I.Null -> (I.Null, id)
      | I.Decl (g, I.BDec (x, (c, s))) ->
          let g', t' = deblockify g in
          let _, l = I.constBlock c in
          let n = List.length l in
          let g'' = append (g', (l, I.comp s (coerceSub t'))) in
          let t'' = comp t' (Shift n) in
          let i = I.Inst (mkInst n) in
          let t''' = Dot (Block i, t'') in
          (g'', t''')

    and append (g', a) = match a with
      | ([], s) -> g'
      | (d :: l, s) ->
          append (I.Decl (g', I.decSub d s), (l, I.dot1 s))

    let rec whnfFor a1 b1 = match a1, b1 with
      | (All (d, _), t) as ft -> ft
      | (Ex (d, f), t) as ft -> ft
      | (And (f1, f2), t) as ft -> ft
      | FClo (f, t1), t2 -> whnfFor f (comp t1 t2)
      | (World (w, f), t) as ft -> ft
      | (True, _) as ft -> ft

    let rec normalizePrg a1 b1 = match a1, b1 with
      | Var n, t ->
          begin match varSub n t with
          | Prg p -> p
          | Idx _ -> raise Domain
          | Exp _ -> raise Domain
          | Block _ -> raise Domain
          | Undef -> raise Domain
          end
      | PairExp (u, p'), t ->
          PairExp (Whnf.normalize (u, coerceSub t), normalizePrg p' t)
      | PairBlock (b, p'), t ->
          PairBlock (I.blockSub b (coerceSub t), normalizePrg p' t)
      | PairPrg (p1, p2), t ->
          PairPrg (normalizePrg p1 t, normalizePrg p2 t)
      | Unit, _ -> Unit
      | EVar (_, { contents = Some p }, _, _, _, _), t -> PClo (p, t)
      | (EVar _ as p), t -> PClo (p, t)
      | Lam (d, p), t -> Lam (normalizeDec d t, normalizePrg p (dot1 t))
      | Rec (d, p), t -> Rec (normalizeDec d t, normalizePrg p (dot1 t))
      | PClo (p, t), t' -> normalizePrg p (comp t t')

    and normalizeSpine a1 b1 = match a1, b1 with
      | Nil, t -> Nil
      | AppExp (u, s), t ->
          AppExp (Whnf.normalize (u, coerceSub t), normalizeSpine s t)
      | AppPrg (p, s), t ->
          AppPrg (normalizePrg p t, normalizeSpine s t)
      | AppBlock (b, s), t ->
          AppBlock (I.blockSub b (coerceSub t), normalizeSpine s t)
      | SClo (s, t1), t2 -> normalizeSpine s (comp t1 t2)

    and normalizeDec a1 b1 = match a1, b1 with
      | PDec (name, f, tc1, None), t ->
          PDec
            ( name,
              forSub f t,
              normalizeTCOpt (tCSubOpt (tc1, coerceSub t)),
              None )
      | UDec d, t -> UDec (Whnf.normalizeDec d (coerceSub t))

    let rec normalizeSub = function
      | Shift n as s -> s
      | Dot (Prg p, s) -> Dot (Prg (normalizePrg p id), normalizeSub s)
      | Dot (Exp e, s) -> Dot (Exp (Whnf.normalize (e, I.id)), normalizeSub s)
      | Dot (Block k, s) -> Dot (Block k, normalizeSub s)
      | Dot (Idx k, s) -> Dot (Idx k, normalizeSub s)

    let rec derefPrg = function
      | Var n -> Var n
      | PairExp (u, p') -> PairExp (u, derefPrg p')
      | PairBlock (b, p') -> PairBlock (b, derefPrg p')
      | PairPrg (p1, p2) -> PairPrg (derefPrg p1, derefPrg p2)
      | Unit -> Unit
      | EVar (_, { contents = Some p }, _, _, _, _) -> p
      | EVar _ as p -> p
      | Lam (d, p) -> Lam (derefDec d, derefPrg p)
      | Rec (d, p) -> Rec (derefDec d, derefPrg p)
      | Redex (p, s) -> Redex (derefPrg p, derefSpine s)
      | Case (Cases cs) ->
          Case
            (Cases
               (flattenCases
                  (map (function psi, s, p -> (psi, s, derefPrg p)) cs)))
      | Let (d, p1, p2) -> Let (derefDec d, derefPrg p1, derefPrg p2)
      | LetPairExp (d1, d2, p1, p2) ->
          LetPairExp (d1, derefDec d2, derefPrg p1, derefPrg p2)
      | LetUnit (p1, p2) -> LetUnit (derefPrg p1, derefPrg p2)

    and flattenCases = function
      | (psi, s, Case (Cases l)) :: cs ->
          map
            (function psi', s', p' -> (psi', comp s s', p'))
            (flattenCases l)
          @ flattenCases cs
      | (psi, s, p) :: cs -> (psi, s, p) :: flattenCases cs
      | [] -> []

    and derefSpine = function
      | Nil -> Nil
      | AppExp (u, s) -> AppExp (u, derefSpine s)
      | AppPrg (p, s) -> AppPrg (derefPrg p, derefSpine s)
      | AppBlock (b, s) -> AppBlock (b, derefSpine s)

    and derefDec = function
      | PDec (name, f, tc1, tc2) -> PDec (name, f, tc1, tc2)
      | UDec d -> UDec d
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
  let tCSub tc s = tCSub_ (tc, s)
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

module Tomega : TOMEGA = MakeTomega (Whnf__) (Conv__)
include Tomega

let () =
  Printexc.register_printer (function NoMatch -> Some "No match" | _ -> None)
