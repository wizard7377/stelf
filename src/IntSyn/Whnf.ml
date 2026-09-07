
(* # 1 "src/lambda/Whnf.sig.ml" *)
open Intsyn_

(* Weak Head-Normal Forms *)
(* Authors: Frank Pfenning, Carsten Schuermann *)
include WHNF
(* signature WHNF *)

(* # 1 "src/lambda/Whnf.fun.ml" *)
open! Basis
open Intsyn_

(* Weak Head-Normal Forms *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
module Whnf () : WHNF = struct
  (*! structure IntSyn = IntSyn' !*)
  (*
     Weak Head-Normal Form (whnf)

     whnf ::= (L, s) | (Pi DP. U, s) | (Root (#k(b), S))
            | (Root(n,S), id) | (Root(c,S), id) | (Root(d,S), id) | (Root(F[s'], S), id)
            | (Root(fgnC,S), id) where fgnC is a foreign constant
            | (Lam D. U, s) | (X, s) where X is uninstantiated, X of base type
                                     during type reconstruction, X might have variable type
            | (FgnExp, id) where FgnExp is a foreign expression

     Normal Form (nf)

        UA ::= L | Pi (DA,P). UA
             | Root(n,SA) | Root(c,SA) | Root(d,SA) | Root(fgnC,SA) | Root (#k(b), S)
             | Lam DA. UA | FgnExp
        DA ::= x:UA
        SA ::= Nil | App (UA, SA)

     Existential Normal Form (enf)

     Existential normal forms are like normal forms, but also allows
     X[s] where X is uninstantiated with no particular restriction on s
     or type of X.

     An existential normal form is a hereditary weak head-normal form.
  *)
  open! struct
    open IntSyn

    exception Eta

    let rec etaContract = function
      | Root (BVar k, s_), s, n ->
          begin match bvarSub k s with
          | Idx k' ->
              begin if k' > n then begin
                etaContract' (s_, s, n);
                k' - n
              end
              else raise Eta
              end
          | _ -> raise Eta
          end
      | Lam (d, u), s, n -> etaContract (u, dot1 s, n + 1)
      | EClo (u, s'), s, n -> etaContract (u, comp s' s, n)
      | EVar ({ contents = Some u }, _, _, _), s, n -> etaContract (u, s, n)
      | AVar { contents = Some u }, s, n -> etaContract (u, s, n)
      | _ -> raise Eta

    and etaContract' = function
      | Nil, s, 0 -> ()
      | App (u, s_), s, n ->
          begin if etaContract (u, s, 0) = n then etaContract' (s_, s, n - 1)
          else raise Eta
          end
      | SClo (s_, s'), s, n -> etaContract' (s_, comp s' s, n)
      | _ -> raise Eta

    let dotEta a1 b1 = match a1, b1 with
      | (Idx _ as ft), s -> Dot (ft, s)
      | (Exp u as ft), s ->
          let ft' = try Idx (etaContract (u, id, 0)) with Eta -> ft in
          Dot (ft', s)
      | (Undef as ft), s -> Dot (ft, s)

    let rec appendSpine = function
      | (Nil, s1), (s2_, s2) -> SClo (s2_, s2)
      | (App (u1, s1_), s1), ss2 ->
          App (EClo (u1, s1), appendSpine ((s1_, s1), ss2))
      | (SClo (s1_, s1'), s1), ss2 -> appendSpine ((s1_, comp s1' s1), ss2)

    let rec whnfRedex = function
      | us, (SClo (s, s2'), s2) -> whnfRedex (us, (s, comp s2' s2))
      | ((Root (h, s) as us1), s1), (Nil, s2) -> (us1, s1)
      | (Root (h1, s1_), s1), (s2_, s2) ->
          (Root (h1, appendSpine ((s1_, s1), (s2_, s2))), id)
      | (Lam (_, u1), s1), (App (u2, s), s2) ->
          whnfRedex (whnf (u1, dotEta (frontSub (Exp u2) s2) s1), (s, s2))
      | ((Lam _, s1) as us), _ -> us
      | ((EVar _, s1) as us), (Nil, s2) -> us
      | (((EVar _ as x), s1) as us), ss2 -> begin
          ignore (lowerEVar x);
          whnfRedex (whnf us, ss2)
        end
      | ((AVar { contents = Some u }, s1) as us), ss2 ->
          whnfRedex ((u, s1), ss2)
      | ((AVar { contents = None }, s1) as us), ss2 -> us
      | ((FgnExp _, _) as us), _ -> us
      | ((Uni _, s1) as us), _ -> us
      | ((Pi _, s1) as us), _ -> us

    and lowerEVar' (g, a) = match a with
      | (Pi ((d', _), v'), s') ->
          let d'' = decSub d' s' in
          let x', u =
            lowerEVar' (Decl (g, d''), whnfExpandDef (v', dot1 s'))
          in
          (x', Lam (d'', u))
      | (v, s) ->
          let x' = newEVar g (EClo (v, s)) in
          (x', x')

    and lowerEVar1 = function
      | EVar (r, g, _, _), ((Pi _, _) as vs) ->
          let x', u = lowerEVar' (g, vs) in
          ignore (r := Some u);
          x'
      | x, _ -> x

    and lowerEVar = function
      | EVar (r, g, v, { contents = [] }) as x ->
          lowerEVar1 (x, whnfExpandDef (v, id))
      | EVar _ ->
          raise
            (Error
               "Typing ambiguous -- constraint of functional type cannot be \
                simplified")

    and whnfRoot (a, s) = match a with
      | (BVar k, s_) ->
          begin match bvarSub k s with
          | Idx k -> (Root (BVar k, SClo (s_, s)), id)
          | Exp u -> whnfRedex (whnf (u, id), (s_, s))
          end
      | (Proj ((Bidx _ as b), i), s_) ->
          begin match blockSub b s with
          | Bidx k as b' -> (Root (Proj (b', i), SClo (s_, s)), id)
          | LVar _ as b' -> whnfRoot ((Proj (b', i), SClo (s_, s)), id)
          | Inst l -> whnfRedex (whnf (List.nth (l, i - 1), id), (s_, s))
          end
      | (Proj (LVar ({ contents = Some b }, sk, (l, t)), i), s_) ->
          whnfRoot ((Proj (blockSub b (comp sk s), i), SClo (s_, s)), id)
      | (Proj ((LVar (r, sk, (l, t)) as l_), i), s_) ->
          (Root (Proj (LVar (r, comp sk s, (l, t)), i), SClo (s_, s)), id)
      | (FVar (name, v, s'), s_) ->
          (Root (FVar (name, v, comp s' s), SClo (s_, s)), id)
      | (NSDef d, s_) -> whnfRedex (whnf (IntSyn.constDef d, id), (s_, s))
      | (h, s_) -> (Root (h, SClo (s_, s)), id)

    and whnf = function
      | (Uni _ as u), s -> (u, s)
      | (Pi _ as u), s -> (u, s)
      | Root (h, s_), s -> whnfRoot ((h, s_), s)
      | Redex (u, s_), s -> whnfRedex (whnf (u, s), (s_, s))
      | (Lam _, s) as us -> us
      | AVar { contents = Some u }, s -> whnf (u, s)
      | (AVar _, s) as us -> us
      | EVar ({ contents = Some u }, _, _, _), s -> whnf (u, s)
      | (EVar (r, _, Root _, _), s) as us -> us
      | (EVar (r, _, Uni _, _), s) as us -> us
      | ((EVar (r, _, v, _) as x), s) as us ->
          begin match whnf (v, id) with
          | Pi _, _ -> begin
              ignore (lowerEVar x);
              whnf us
            end
          | _ -> us
          end
      | EClo (u, s'), s -> whnf (u, comp s' s)
      | (FgnExp _, Shift 0) as us -> us
      | (FgnExp (csid, fge), s) as us ->
          (FgnExpStd.Map.apply csid fge (function u -> EClo (u, s)), id)

    and expandDef (Root (Def d, s_), s) =
      whnfRedex (whnf (constDef d, id), (s_, s))

    and whnfExpandDefW = function
      | (Root (Def _, _), _) as us -> whnfExpandDefW (expandDef us)
      | us -> us

    and whnfExpandDef us = whnfExpandDefW (whnf us)

    let rec newLoweredEVarW (g, a) = match a with
      | (Pi ((d, _), v), s) ->
          let d' = decSub d s in
          Lam (d', newLoweredEVar (Decl (g, d')) (v, dot1 s))
      | (v, s) -> newEVar g (EClo (v, s))

    and newLoweredEVar g vs = newLoweredEVarW (g, whnfExpandDef vs)

    let rec newSpineVarW (g, a) = match a with
      | (Pi ((Dec (_, va), _), vr), s) ->
          let x = newLoweredEVar g (va, s) in
          App (x, newSpineVar g (vr, dotEta (Exp x) s))
      | _ -> Nil

    and newSpineVar g vs = newSpineVarW (g, whnfExpandDef vs)

    let rec spineToSub a1 b1 = match a1, b1 with
      | Nil, s -> s
      | App (u, s_), s -> spineToSub s_ (dotEta (Exp u) s)

    let rec inferSpine = function
      | (Nil, _), vs -> vs
      | (SClo (s_, s'), s), vs -> inferSpine ((s_, comp s' s), vs)
      | (App (u, s), s1), (Pi (_, v2), s2) ->
          inferSpine
            ((s, s1), whnfExpandDef (v2, Dot (Exp (EClo (u, s1)), s2)))

    let inferCon = function
      | Const cid -> constType cid
      | Skonst cid -> constType cid
      | Def cid -> constType cid

    let rec etaExpand' (u, a) = match a with
      | (Root _, s) -> u
      | (Pi ((d, _), v), s) ->
          Lam
            ( decSub d s,
              etaExpand'
                ( Redex (EClo (u, shift), App (Root (BVar 1, Nil), Nil)),
                  whnfExpandDef (v, dot1 s) ) )

    let etaExpandRoot (Root (h, s) as u) =
      etaExpand' (u, inferSpine ((s, id), (inferCon h, id)))

    let rec whnfEta us vs = whnfEtaW (whnf us, whnf vs)

    and whnfEtaW = function
      | (_, (Root _, _)) as usVs -> usVs
      | ((Lam _, _), (Pi _, _)) as usVs -> usVs
      | (u, s1), ((Pi ((d, p), v), s2) as vs2) ->
          ( ( Lam
                ( decSub d s2,
                  Redex
                    (EClo (u, comp s1 shift), App (Root (BVar 1, Nil), Nil))
                ),
              id ),
            vs2 )

    let rec normalizeExp us = normalizeExpW (whnf us)

    and normalizeExpW = function
      | (Uni l as u), s -> u
      | Pi (dp, u), s -> Pi (normalizeDecP (dp, s), normalizeExp (u, dot1 s))
      | (Root (h, s_) as u), s -> Root (h, normalizeSpine s_ s)
      | Lam (d, u), s -> Lam (normalizeDec d s, normalizeExp (u, dot1 s))
      | (EVar (_, _, _, _) as e), s -> EClo (e, s)
      | FgnExp (csid, fge), s ->
          FgnExpStd.Map.apply csid fge (function u -> normalizeExp (u, s))
      | (AVar { contents = Some u }, s) as us -> normalizeExpW (u, s)
      | (AVar _, s) as us -> begin
          print "Normalize  AVAR\n";
          raise (Error "")
        end

    and normalizeSpine a1 b1 = match a1, b1 with
      | Nil, s -> Nil
      | App (u, s_), s -> App (normalizeExp (u, s), normalizeSpine s_ s)
      | SClo (s_, s'), s -> normalizeSpine s_ (comp s' s)

    and normalizeDec a1 b1 = match a1, b1 with
      | Dec (xOpt, v), s -> Dec (xOpt, normalizeExp (v, s))
      | BDec (xOpt, (c, t)), s -> BDec (xOpt, (c, normalizeSub (comp t s)))

    and normalizeDecP ((d, p), s) = (normalizeDec d s, p)

    and normalizeSub = function
      | Shift _ as s -> s
      | Dot ((Idx _ as ft), s) -> Dot (ft, normalizeSub s)
      | Dot (Exp u, s) -> dotEta (Exp (normalizeExp (u, id))) (normalizeSub s)

    let rec normalizeCtx = function
      | Null -> Null
      | Decl (g, d) -> Decl (normalizeCtx g, normalizeDec d id)

    let invert s =
      let rec lookup (n, a, p) = match a with
        | Shift _ -> None
        | Dot (Undef, s') -> lookup (n + 1, s', p)
        | Dot (Idx k, s') ->
            begin if k = p then Some n else lookup (n + 1, s', p)
            end
      in
      let rec invert'' (p, si) = match p with
        | 0 -> si
        | p ->
            begin match lookup (1, s, p) with
            | Some k -> invert'' (p - 1, Dot (Idx k, si))
            | None -> invert'' (p - 1, Dot (Undef, si))
            end
      in
      let rec invert' (n, a) = match a with
        | Shift p -> invert'' (p, Shift n)
        | Dot (_, s') -> invert' (n + 1, s')
      in
      invert' (0, s)

    let rec strengthen a1 b1 = match a1, b1 with
      | Shift n, Null -> Null
      | Dot (Idx k, t), Decl (g, d) ->
          let t' = comp t invShift in
          Decl (strengthen t' g, decSub d t')
      | Dot (Undef, t), Decl (g, d) -> strengthen t g
      | Shift n, g -> strengthen (Dot (Idx (n + 1), Shift (n + 1))) g

    let rec isId' = function
      | Shift k, k' -> k = k'
      | Dot (Idx n, s'), k' -> n = k' && isId' (s', k' + 1)
      | _ -> false

    let isId s = isId' (s, 0)
    let cloInv u w = EClo (u, invert w)
    let compInv s w = comp s (invert w)

    let rec isPatSub = function
      | Shift k -> true
      | Dot (Idx n, s) ->
          let rec checkBVar = function
            | Shift k -> n <= k
            | Dot (Idx n', s) -> n <> n' && checkBVar s
            | Dot (Undef, s) -> checkBVar s
            | _ -> false
          in
          checkBVar s && isPatSub s
      | Dot (Undef, s) -> isPatSub s
      | _ -> false

    let rec mkPatSub = function
      | Shift k as s -> s
      | Dot (Idx n, s) ->
          let s' = mkPatSub s in
          let rec checkBVar = function
            | Shift k -> n <= k
            | Dot (Idx n', s') -> n <> n' && checkBVar s'
            | Dot (Undef, s') -> checkBVar s'
          in
          ignore (checkBVar s');
          Dot (Idx n, s')
      | Dot (Undef, s) -> Dot (Undef, mkPatSub s)
      | Dot (Exp u, s) ->
          let u', t' = whnf (u, id) in
          let k = etaContract (u', t', 0) in
          Dot (Idx k, mkPatSub s)
      | _ -> raise Eta

    let makePatSub s = try Some (mkPatSub s) with Eta -> None
  end

  (* exception Undefined *)
  (* etaContract (U, s, n) = k'

       Invariant:
       if   G, V1, .., Vn |- s : G1  and  G1 |- U : V
       then if   lam V1...lam Vn. U[s] =eta*=> k
            then k' = k
            and  G |- k' : Pi V1...Pi Vn. V [s]
            else Eta is raised
              (even if U[s] might be eta-reducible to some other expressions).
    *)
  (* optimization(?): quick check w/o substitution first *)
  (* Should fail: (c@S), (d@S), (F@S), X *)
  (* Not treated (fails): U@S *)
  (* Could weak head-normalize for more thorough checks *)
  (* Impossible: L, Pi D.V *)
  (* etaContract' (S, s, n) = R'

       Invariant:
       If  G |- s : G1    and  G1 |- S : V > W
       then if   S[s] =eta*=> n ; n-1 ; ... ; 1 ; Nil
            then ()
       else Eta is raised
    *)
  (* dotEta (Ft, s) = s'

       Invariant:
       If   G |- s : G1, V  and G |- Ft : V [s]
       then Ft  =eta*=>  Ft1
       and  s' = Ft1 . s
       and  G |- s' : G1, V
    *)
  (* appendSpine ((S1, s1), (S2, s2)) = S'

       Invariant:
       If    G |- s1 : G1   G1 |- S1 : V1' > V1
       and   G |- s2 : G2   G2 |- S2 : V2  > V2'
       and   G |- V1 [s1] == V2 [s2]
       then  G |- S' : V1' [s1] > V2' [s2]
    *)
  (* whnfRedex ((U, s1), (S, s2)) = (U', s')

       Invariant:
       If    G |- s1 : G1   G1 |- U : V1,   (U,s1) whnf
             G |- s2 : G2   G2 |- S : V2 > W2
             G |- V1 [s1] == V2 [s2] == V : L
       then  G |- s' : G',  G' |- U' : W'
       and   G |- W'[s'] == W2[s2] == W : L
       and   G |- U'[s'] == (U[s1] @ S[s2]) : W
       and   (U',s') whnf

       Effects: EVars may be lowered to base type.
    *)
  (* S2 = App _, only possible if term is not eta-expanded *)
  (* S2[s2] = Nil *)
  (* Ss2 must be App, since prior cases do not apply *)
  (* lowerEVar X results in redex, optimize by unfolding call to whnfRedex *)
  (* Uni and Pi can arise after instantiation of EVar X : K *)
  (* S2[s2] = Nil *)
  (* S2[s2] = Nil *)
  (* Other cases impossible since (U,s1) whnf *)
  (* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)
  (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)
  (* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *)
  (* It is not clear if this case can happen *)
  (* pre-Stelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
  (* whnfRoot ((H, S), s) = (U', s')

       Invariant:
       If    G |- s : G1      G1 |- H : V
                              G1 |- S : V > W
       then  G |- s' : G'     G' |- U' : W'
       and   G |- W [s] = W' [s'] : L

       Effects: EVars may be instantiated when lowered
    *)
  (* Undef should be impossible *)
  (* could blockSub (B, s) return instantiated LVar ? *)
  (* Sat Dec  8 13:43:17 2001 -fp !!! *)
  (* yes Thu Dec 13 21:48:10 2001 -fp !!! *)
  (* was: (Root (Proj (blockSub (B, s), i), SClo (S, s)), id) *)
  (* r = ref NONE *)
  (* scary: why is comp(sk, s) = ^n ?? -fp July 22, 2010, -fp -cs *)
  (* was:
         (Root (Proj (LVar (r, comp (sk, s), (l, comp(t, s))), i), SClo (S, s)), id)
         Jul 22, 2010 -fp -cs
         *)
  (* do not compose with t due to globality invariant *)
  (* Thu Dec  6 20:34:30 2001 -fp !!! *)
  (* was: (Root (Proj (L, i), SClo (S, s)), id) *)
  (* going back to first version, because globality invariant *)
  (* no longer satisfied Wed Nov 27 09:49:58 2002 -fp *)
  (* Undef and Exp should be impossible by definition of substitution -cs *)
  (* whnf (U, s) = (U', s')

       Invariant:
       If    G |- s : G'    G' |- U : V
       then  G |- s': G''   G''|- U' : V'
       and   G |- V [s] == V' [s'] == V'' : L
       and   G |- U [s] == U' [s'] : V''
       and   (U', s') whnf
    *)
  (*
       Possible optimization :
         Define whnf of Root as (Root (n , S [s]), id)
         Fails currently because appendSpine does not necessairly return a closure  -cs
         Advantage: in unify, Abstract... the spine needn't be treated under id, but under s
    *)
  (* simple optimization (C@S)[id] = C@S[id] *)
  (* applied in Stelf 1.1 *)
  (* Sat Feb 14 20:53:08 1998 -fp *)
  (*      | whnf (Us as (Root _, Shift (0))) = Us*)
  (* commented out, because non-strict definitions slip
         Mon May 24 09:50:22 EDT 1999 -cs  *)
  (* | whnf (Us as (EVar _, s)) = Us *)
  (* next two avoid calls to whnf (V, id), where V is type of X *)
  (* possible opt: call lowerEVar1 *)
  (* expandDef (Root (Def (d), S), s) = (U' ,s')

       Invariant:
       If    G |- s : G1     G1 |- S : V > W            ((d @ S), s) in whnf
                             .  |- d = U : V'
       then  G |- s' : G'    G' |- U' : W'
       and   G |- V' == V [s] : L
       and   G |- W' [s'] == W [s] == W'' : L
       and   G |- (U @ S) [s] == U' [s'] : W'
       and   (U', s') in whnf
    *)
  (* why the call to whnf?  isn't constDef (d) in nf? -kw *)
  (* inferSpine ((S, s1), (V, s2)) = (V', s')

       Invariant:
       If  G |- s1 : G1  and  G1 |- S : V1 > V1'
       and G |- s2 : G2  and  G2 |- V : L,  (V, s2) in whnf
       and G |- S[s1] : V[s2] > W  (so V1[s1] == V[s2] and V1[s1] == W)
       then G |- V'[s'] = W
    *)
  (* FIX: this is almost certainly mis-design -kw *)
  (* inferCon (C) = V  if C = c or C = d or C = sk and |- C : V *)
  (* FIX: this is almost certainly mis-design -kw *)
  (* etaExpand' (U, (V,s)) = U'

       Invariant :
       If    G |- U : V [s]   (V,s) in whnf
       then  G |- U' : V [s]
       and   G |- U == U' : V[s]
       and   (U', id) in whnf and U' in head-eta-long form
    *)
  (* quite inefficient -cs *)
  (* FIX: this is almost certainly mis-design -kw *)
  (* etaExpandRoot (Root(H, S)) = U' where H = c or H = d

       Invariant:
       If   G |- H @ S : V  where H = c or H = d
       then G |- U' : V
       and  G |- H @ S == U'
       and (U',id) in whnf and U' in head-eta-long form
    *)
  (* FIX: this is almost certainly mis-design -kw *)
  (* whnfEta ((U, s1), (V, s2)) = ((U', s1'), (V', s2)')

       Invariant:
       If   G |- s1 : G1  G1 |- U : V1
       and  G |- s2 : G2  G2 |- V : L
       and  G |- V1[s1] == V[s2] : L

       then G |- s1' : G1'  G1' |- U' : V1'
       and  G |- s2' : G2'  G2' |- V' : L'
       and  G |- V1'[s1'] == V'[s2'] : L
       and (U', s1') is in whnf
       and (V', s2') is in whnf
       and (U', s1') == Lam x.U'' if V[s2] == Pi x.V''

       Similar to etaExpand', but without recursive expansion
    *)
  (* FIX: this is almost certainly mis-design -kw *)
  (* Invariant:

       normalizeExp (U, s) = U'
       If   G |- s : G' and G' |- U : V
       then U [s] = U'
       and  U' in existential normal form

       If (U, s) contain no existential variables,
       then U' in normal formal
    *)
  (* s = id *)
  (* dead code -fp *)
  (* pre-Stelf 1.2 code walk Fri May  8 11:37:18 1998 *)
  (* not any more --cs Wed Jun 19 13:59:56 EDT 2002 *)
  (* changed to obtain pattern substitution if possible *)
  (* Sat Dec  7 16:58:09 2002 -fp *)
  (* Dot (Exp (normalizeExp (U, id)), normalizeSub s) *)
  (* invert s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id
    *)
  (* strengthen (t, G) = G'

       Invariant:
       If   G'' |- t : G     and t strsub 
       then G' |- t : G  and G' subcontext of G
    *)
  (* = 0 *)
  (* k = 1 *)
  (* G |- D dec *)
  (* G' |- t' : G *)
  (* G' |- D[t'] dec *)
  (* isId s = B

       Invariant:
       If   G |- s: G', s weakensub
       then B holds
            iff s = id, G' = G
    *)
  (* cloInv (U, w) = U[w^-1]

       Invariant:
       If G |- U : V
          G |- w : G'  w weakening subst
          U[w^-1] defined (without pruning or constraints)

       then G' |- U[w^-1] : V[w^-1]
       Effects: None
    *)
  (* cloInv (s, w) = s o w^-1

       Invariant:
       If G |- s : G1
          G |- w : G2  s weakening subst
          s o w^-1 defined (without pruning or constraints)

       then G2 |- s o w^-1 : G1
       Effects: None
    *)
  (* functions previously in the Pattern functor *)
  (* eventually, they may need to be mutually recursive with whnf *)
  (* isPatSub s = B

       Invariant:
       If    G |- s : G'
       and   s = n1 .. nm ^k
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k or ni = _ for all 1 <= i <= m
    *)
  (* Try harder, due to bug somewhere *)
  (* Sat Dec  7 17:05:02 2002 -fp *)
  (* false *)
  (* below does not work, because the patSub is lost *)
  (*
          let val (U', s') = whnf (U, id)
          in
            isPatSub (Dot (Idx (etaContract (U', s', 0)), s))
            handle Eta => false
          end
      | isPatSub _ = false
      *)
  (* makePatSub s = SOME(s') if s is convertible to a patSub
                      NONE otherwise

       Invariant:
       If    G |- s : G'
       and   s = n1 .. nm ^k
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k or ni = _ for all 1 <= i <= m
    *)
  (* may raise Eta *)
  let isPatSub = isPatSub
  let makePatSub = makePatSub
  let dotEta = dotEta

  exception Eta = Eta

  let etaContract u = etaContract (u, IntSyn.id, 0)
  let whnf = whnf
  let expandDef = expandDef
  let whnfExpandDef = whnfExpandDef
  let etaExpandRoot = etaExpandRoot
  let whnfEta = whnfEta
  let lowerEVar = lowerEVar
  let newLoweredEVar = newLoweredEVar
  let newSpineVar = newSpineVar
  let spineToSub = spineToSub
  let normalize = normalizeExp
  let normalizeDec = normalizeDec
  let normalizeCtx = normalizeCtx
  let invert = invert
  let strengthen = strengthen
  let isId = isId
  let cloInv = cloInv
  let compInv = compInv
end
(*! structure IntSyn' : INTSYN !*)
(* functor Whnf *)

(* # 1 "src/lambda/Whnf.sml.ml" *)
