open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Subordinate
open! Typecheck.Typecheck_
open! Index.Index_
open! Heuristic.Heuristic_
open! Solvers.Solvers_

(* # 1 "src/meta/Splitting.sig.ml" *)
open Funsyn
open Statesyn
open MtpGlobal
open MtpAbstract
open MtpPrint
open Funtypecheck

(* Splitting : Version 1.3 *)
(* Author: Carsten Schuermann *)
include MTPSPLITTING
(* signature MTPSPLITTING *)

(* # 1 "src/meta/Splitting.fun.ml" *)
open! Basis

(* Splitting : Version 1.3 *)
(* Author: Carsten Schuermann *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MTPSplitting (MTPSplitting__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn !*)
  module StateSyn' : STATESYN.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn !*)
  (*! sharing StateSyn'.IntSyn = IntSyn !*)
  module Heuristic : HEURISTIC
  module MTPAbstract : MTPABSTRACT.MTPABSTRACT

  (*! sharing MTPAbstract.IntSyn = IntSyn !*)
  module MTPrint : MTPPRINT.MTPRINT
  module Names : NAMES

  (* too be removed  -cs *)
  (*! sharing Names.IntSyn = IntSyn !*)
  (* too be removed  -cs *)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn !*)
  module Subordinate : Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn !*)
  module FunTypeCheck : FUNTYPECHECK.FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : MTPSPLITTING.MTPSPLITTING = struct
  open MTPSplitting__0
  module StateSyn = StateSyn'

  exception Error = Error

  (* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given State.

     'a flag marks cases where unification of the types
     succeeded as ""Active"", and cases where there were
     leftover constraints after unification as ""Inactive"".

     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases (this
     can be checked for a given operator by applicable)
  *)
  type 'a flag = Active of 'a | InActive [@@deriving eq, ord, show]

  type operator_ =
    | Operator of
        (StateSyn.state * int) * StateSyn.state flag list * Heuristic.index

  type nonrec operator = operator_

  open! struct
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn
    module H = Heuristic

    let makeOperator (a, l, b, g, i, m, d) = match a, b, d with
      | (s, k), S.Splits n, true ->
          Operator
            ( (s, k),
              l,
              { sd = n; ind = i; c = List.length l; m; r = 1; p = g + 1 } )
      | (s, k), S.Splits n, false ->
          Operator
            ( (s, k),
              l,
              { sd = n; ind = i; c = List.length l; m; r = 0; p = g + 1 } )

    let rec aux = function
      | I.Null, I.Null -> I.Null
      | I.Decl (g, d), I.Decl (b, S.Lemma _) ->
          I.Decl (aux (g, b), F.Prim d)
      | (I.Decl (_, d) as g), (I.Decl (_, S.Parameter (Some l)) as b) ->
          let (F.LabelDec (name, _, g2)) = F.labelLookup l in
          let psi', g' = aux' (g, b, List.length g2) in
          I.Decl (psi', F.Block (F.CtxBlock (Some l, g')))

    and aux' = function
      | g, b, 0 -> (aux (g, b), I.Null)
      | I.Decl (g, d), I.Decl (b, S.Parameter (Some _)), n ->
          let psi', g' = aux' (g, b, n - 1) in
          (psi', I.Decl (g', d))

    let conv gs gs' =
      let exception Conv in
      let rec conv a1 b1 = match a1, b1 with
        | (I.Null, s), (I.Null, s') -> (s, s')
        | (I.Decl (g, I.Dec (_, v)), s), (I.Decl (g', I.Dec (_, v')), s') ->
            let s1, s1' = conv (g, s) (g', s') in
            let ((s2, s2') as ps) = (I.dot1 s1, I.dot1 s1') in
            begin if Conv.conv (v, s1) (v', s1') then ps else raise Conv
            end
        | _ -> raise Conv
      in
      try
        begin
          ignore (conv gs gs');
          true
        end
      with Conv -> false

    let rec createEVarSpine (g, vs) = createEVarSpineW (g, Whnf.whnf vs)

    and createEVarSpineW (g, a) = match a with
      | ((I.Uni I.Type, s) as vs) -> (I.Nil, vs)
      | ((I.Root _, s) as vs) -> (I.Nil, vs)
      | (I.Pi (((I.Dec (_, v1) as d), _), v2), s) ->
          let x = I.newEVar g (I.EClo (v1, s)) in
          let s_, vs = createEVarSpine (g, (v2, I.Dot (I.Exp x, s))) in
          (I.App (x, s_), vs)

    let createAtomConst g h =
      let cid =
        begin match h with
        | I.Const cid -> cid
        | I.Skonst cid -> cid
        | I.Def cid -> cid
        | _ -> assert false
        end
      in
      let v = I.constType cid in
      let s, vs = createEVarSpine (g, (v, I.id)) in
      (I.Root (h, s), vs)

    let createAtomBVar g k =
      let (I.Dec (_, v)) = I.ctxDec g k in
      let s, vs = createEVarSpine (g, (v, I.id)) in
      (I.Root (I.BVar k, s), vs)

    let rec someEVars (g, a, s) = match a with
      | [] -> s
      | I.Dec (_, v) :: l ->
          someEVars (g, l, I.Dot (I.Exp (I.newEVar g (I.EClo (v, s))), s))

    let maxNumberParams a =
      let rec maxNumberParams' n =
        begin if n < 0 then 0
        else
          let (F.LabelDec (name, g1, g2)) = F.labelLookup n in
          let m' =
            foldr
              (function
                | I.Dec (_, v), m ->
                    begin if I.targetFam v = a then m + 1 else m
                    end)
              0 g2
          in
          maxNumberParams' (n - 1) + m'
        end
      in
      maxNumberParams' (F.labelSize () - 1)

    let rec maxNumberLocalParams (b, a) = match b with
      | I.Pi ((I.Dec (_, v1), _), v2) ->
          let m = maxNumberLocalParams (v2, a) in
          begin if I.targetFam v1 = a then m + 1 else m
          end
      | I.Root _ -> 0

    let maxNumberConstCases a = List.length (Index.lookup a)

    let maxNumberCases (v, a) =
      maxNumberParams a + maxNumberLocalParams (v, a) + maxNumberConstCases a

    let rec ctxSub (a, s) = match a with
      | [] -> []
      | d :: g -> I.decSub d s :: ctxSub (g, I.dot1 s)

    let rec createTags (n, l) = match n with
      | 0 -> I.Null
      | n -> I.Decl (createTags (n - 1, l), S.Parameter (Some l))

    let rec createLemmaTags = function
      | I.Null -> I.Null
      | I.Decl (g, d) ->
          I.Decl (createLemmaTags g, S.Lemma (S.Splits !MTPGlobal.maxSplit))

    let rec constCases (g, vs, a, abstract, ops) = match a with
      | [] -> ops
      | (I.Const c as h) :: sgn ->
          let u, vs' = createAtomConst g h in
          constCases
            ( g,
              vs,
              sgn,
              abstract,
              CsManager.trail (function () ->
                  (try
                     begin if Unify.unifiable g vs vs' then
                       Active (abstract u) :: ops
                     else ops
                     end
                   with MTPAbstract.Error _ -> InActive :: ops)) )
      | (I.Def c as h) :: sgn ->
          let u, vs' = createAtomConst g h in
          constCases
            ( g,
              vs,
              sgn,
              abstract,
              CsManager.trail (function () ->
                  (try
                     begin if Unify.unifiable g vs vs' then
                       Active (abstract u) :: ops
                     else ops
                     end
                   with MTPAbstract.Error _ -> InActive :: ops)) )
      | _ :: sgn ->
          (* Skip other head types *)
          constCases (g, vs, sgn, abstract, ops)

    let rec paramCases (g, vs, k, abstract, ops) = match k with
      | 0 -> ops
      | k ->
          let u, vs' = createAtomBVar g k in
          paramCases
            ( g,
              vs,
              k - 1,
              abstract,
              CsManager.trail (function () ->
                  (try
                     begin if Unify.unifiable g vs vs' then
                       Active (abstract u) :: ops
                     else ops
                     end
                   with MTPAbstract.Error _ -> InActive :: ops)) )

    let constAndParamCases ops0 (c, g, k, (v, s'), abstract) =
      constCases
        ( g,
          (v, s'),
          Index.lookup c,
          abstract,
          paramCases (g, (v, s'), k, abstract, ops0) )

    let metaCases (d, ops0) (c, g_, k, vs, abstract) =
      let g = I.ctxLength g_ in
      let rec select (d', ops) = match d' with
        | 0 -> ops
        | d' ->
            let n = g - d' + 1 in
            let (I.Dec (_, v)) = I.ctxDec g_ n in
            let ops' =
              begin if I.targetFam v = c then
                let u, vs' = createAtomBVar g_ n in
                CsManager.trail (function () ->
                    (try
                       begin if Unify.unifiable g_ vs vs' then
                         Active (abstract u) :: ops
                       else ops
                       end
                     with MTPAbstract.Error _ -> InActive :: ops))
              else ops
              end
            in
            select (d' - 1, ops')
      in
      select (d, ops0)

    let rec lowerSplitDest (g, k, a, abstract, cases) = match a with
      | ((I.Root (I.Const c, _) as v), s') ->
          cases (c, g, I.ctxLength g, (v, s'), abstract)
      | (I.Pi ((d, p), v), s') ->
          let d' = I.decSub d s' in
          lowerSplitDest
            ( I.Decl (g, d'),
              k + 1,
              (v, I.dot1 s'),
              (fun u -> abstract (I.Lam (d', u))),
              cases )

    let abstractErrorLeft ((g, b), s) =
      raise (MTPAbstract.Error "Cannot split left of parameters")

    let abstractErrorRight ((g, b), s) =
      raise (MTPAbstract.Error "Cannot split right of parameters")

    let split (((I.Dec (_, v) as d), t_), sc, abstract) =
      let rec split' (n, cases) =
        begin if n < 0 then
          let (g', b'), s', (g0, b0), _ = sc (I.Null, I.Null) in
          let abstract' u' =
            let ((g'', b''), s'') : (I.dctx * S.tag I.ctx) * I.sub =
              Obj.magic
                (MTPAbstract.abstractSub'
                   g' b' (I.Dot (I.Exp u', s')) (I.Decl (b0, t_)))
            in
            ignore begin if !Global.doubleCheck then (
                let psi'' = aux (g'', b'') in
                ignore (TypeCheck.typeCheckCtx (F.makectx psi''));
                let psi = aux (Obj.magic (I.Decl (g0, d), I.Decl (b0, t_))) in
                ignore (TypeCheck.typeCheckCtx (F.makectx psi));
                FunTypeCheck.checkSub psi'' s'' psi)
              else ()
              end;
            abstract ((g'', b''), s'')
          in
          lowerSplitDest (g', 0, (v, s'), abstract', constAndParamCases cases)
        else
          let (F.LabelDec (name, g1, g2)) = F.labelLookup n in
          let t = someEVars (I.Null, g1, I.id) in
          let b1 = createLemmaTags (F.listToCtx g1) in
          let g2t = ctxSub (g2, t) in
          let length = List.length g2 in
          let b2 = createTags (length, n) in
          let (g', b'), s', (g0, b0), p =
            sc (Names.ctxName (F.listToCtx g2t), b2)
          in
          let abstract' u' =
            begin if p then
              raise (MTPAbstract.Error "Cannot split right of parameters")
            else
              let ((g'', b''), s'') : (I.dctx * S.tag I.ctx) * I.sub =
                Obj.magic
                  ((Obj.magic MTPAbstract.abstractSub)
                     t b1 (g', b') (I.Dot (I.Exp u', s')) (I.Decl (b0, t_)))
              in
              ignore begin if !Global.doubleCheck then (
                  let psi'' = aux (g'', b'') in
                  ignore (TypeCheck.typeCheckCtx (F.makectx psi''));
                  let psi =
                    aux (Obj.magic (I.Decl (g0, d), I.Decl (b0, t_)))
                  in
                  ignore (TypeCheck.typeCheckCtx (F.makectx psi));
                  FunTypeCheck.checkSub psi'' s'' psi)
                else ()
                end;
              abstract ((g'', b''), s'')
            end
          in
          let cases' =
            lowerSplitDest
              (g', 0, (v, s'), abstract', metaCases (length, cases))
          in
          split' (n - 1, cases')
        end
      in
      split' (F.labelSize () - 1, [])

    let rec occursInExp (k, a) = match a with
      | I.Uni _ -> false
      | I.Pi (dp, v) -> occursInDecP (k, dp) || occursInExp (k + 1, v)
      | I.Root (c, s) -> occursInCon (k, c) || occursInSpine (k, s)
      | I.Lam (d, v) -> occursInDec (k, d) || occursInExp (k + 1, v)
      | I.FgnExp (csid, csfe) ->
          I.FgnExpStd.fold csid csfe
            (function
              | u, b -> b || occursInExp (k, Whnf.normalize (u, I.id)))
            false

    and occursInCon (k, a) = match a with
      | I.BVar k' -> k = k'
      | I.Const _ -> false
      | I.Def _ -> false
      | I.Skonst _ -> false

    and occursInSpine (k, a) = match a with
      | I.Nil -> false
      | I.App (u, s) -> occursInExp (k, u) || occursInSpine (k, s)

    and occursInDec (k, I.Dec (_, v)) = occursInExp (k, v)
    and occursInDecP (k, (d, _)) = occursInDec (k, d)

    let isIndexInit k = false
    let isIndexSucc (d, isIndex) k = occursInDec (k, d) || isIndex (k + 1)
    let isIndexFail (d, isIndex) k = isIndex (k + 1)

    let abstractInit (S.State (n, (g, b), (ih, oh), d, o, h, f) as s)
        ((g', b'), s') =
      begin
        begin if !Global.doubleCheck then TypeCheck.typeCheckCtx g' else ()
        end;
        begin
          begin if !Global.doubleCheck then
            FunTypeCheck.isFor g' (F.forSub f s')
          else ()
          end;
          S.State
            ( n,
              (g', b'),
              (ih, oh),
              d,
              S.orderSub o s',
              map (function i, f' -> (i, F.forSub f' s')) h,
              F.forSub f s' )
        end
      end

    let abstractCont ((d, t), abstract) ((g, b), s) =
      abstract
        ( ( I.Decl (g, Whnf.normalizeDec d s),
            I.Decl (b, S.normalizeTag t s) ),
          I.dot1 s )

    let makeAddressInit s k = (s, k)
    let makeAddressCont makeAddress k = makeAddress (k + 1)

    let rec occursInOrder (n, a, k, sc) = match a with
      | S.Arg (us, vt) ->
          let u' = Whnf.normalize us in
          begin if occursInExp (k, u') then Some n else sc (n + 1)
          end
      | S.Lex os -> occursInOrders (n, os, k, sc)
      | S.Simul os -> occursInOrders (n, os, k, sc)

    and occursInOrders (n, a, k, sc) = match a with
      | [] -> sc n
      | o :: os ->
          occursInOrder
            (n, o, k, function n' -> occursInOrders (n', os, k, sc))

    let inductionInit o k = occursInOrder (0, o, k, function n -> None)
    let inductionCont induction k = induction (k + 1)

    let rec expand' (b, isIndex, abstract, makeAddress, induction) = match b with
      | ((I.Null, I.Null) as gb) ->
          ( (fun (gp, bp) -> ((gp, bp), I.Shift (I.ctxLength gp), gb, false)),
            [] )
      | ((I.Decl (g, d), I.Decl (b, (S.Lemma (S.Splits _ as k) as t))) as
           gb) ->
          let sc, ops =
            expand'
              ( (g, b),
                isIndexSucc (d, isIndex),
                abstractCont ((d, t), abstract),
                makeAddressCont makeAddress,
                inductionCont induction )
          in
          let (I.Dec (xOpt, v)) = d in
          let sc' (gp, bp) =
            let (g', b'), s', (g0, b0), p' = sc (gp, bp) in
            let x = I.newEVar g' (I.EClo (v, s')) in
            ( (g', b'),
              I.Dot (I.Exp x, s'),
              (I.Decl (g0, d), I.Decl (b0, t)),
              p' )
          in
          let ops' =
            begin if (not (isIndex 1)) && S.splitDepth k > 0 then
              let a = I.targetFam v in
              makeOperator
                ( makeAddress 1,
                  split ((d, Obj.magic t), Obj.magic sc, abstract),
                  k,
                  I.ctxLength g,
                  induction 1,
                  maxNumberCases (v, a),
                  Subordinate.below a a )
              :: ops
            else ops
            end
          in
          (sc', ops')
      | (I.Decl (g, d), I.Decl (b, (S.Lemma rl as t))) ->
          let sc, ops =
            expand'
              ( (g, b),
                isIndexSucc (d, isIndex),
                abstractCont ((d, t), abstract),
                makeAddressCont makeAddress,
                inductionCont induction )
          in
          let (I.Dec (xOpt, v)) = d in
          let sc' (gp, bp) =
            let (g', b'), s', (g0, b0), p' = sc (gp, bp) in
            let x = I.newEVar g' (I.EClo (v, s')) in
            ( (g', b'),
              I.Dot (I.Exp x, s'),
              (I.Decl (g0, d), I.Decl (b0, t)),
              p' )
          in
          (sc', ops)
      | (I.Decl (g, d), I.Decl (b, (S.Lemma rLdone as t))) ->
          let sc, ops =
            expand'
              ( (g, b),
                isIndexSucc (d, isIndex),
                abstractCont ((d, t), abstract),
                makeAddressCont makeAddress,
                inductionCont induction )
          in
          let (I.Dec (xOpt, v)) = d in
          let sc' (gp, bp) =
            let (g', b'), s', (g0, b0), p' = sc (gp, bp) in
            let x = I.newEVar g' (I.EClo (v, s')) in
            ( (g', b'),
              I.Dot (I.Exp x, s'),
              (I.Decl (g0, d), I.Decl (b0, t)),
              p' )
          in
          (sc', ops)
      | (I.Decl (g, d), I.Decl (b, (S.Parameter (Some _) as t))) ->
          let sc, ops =
            expand'
              ( (g, b),
                isIndexSucc (d, isIndex),
                abstractErrorLeft,
                makeAddressCont makeAddress,
                inductionCont induction )
          in
          let (I.Dec (xOpt, v)) = d in
          let sc' (gp, bp) =
            let (g', b'), s', (g0, b0), _ = sc (gp, bp) in
            ( ( I.Decl (g', Names.decName g' (I.decSub d s')),
                I.Decl (b', t) ),
              I.dot1 s',
              (I.Decl (g0, d), I.Decl (b0, t)),
              true )
          in
          (sc', ops)

    let expand (S.State (n, (g0, b0), _, _, o, _, _) as s0) =
      ignore begin if !Global.doubleCheck then FunTypeCheck.isState (Obj.magic s0)
        else ()
        end;
      let _, ops =
        expand'
          ( (g0, b0),
            isIndexInit,
            abstractInit s0,
            makeAddressInit s0,
            inductionInit o )
      in
      ops

    let index (Operator ((s, index), sl, { c = k })) = k

    let compare (Operator (_, _, i1)) (Operator (_, _, i2)) =
      H.compare i1 i2

    let isInActive = function Active _ -> false | InActive -> true
    let applicable (Operator (_, sl, i)) = not (List.exists isInActive sl)

    let apply (Operator (_, sl, i)) =
      map
        (function
          | Active s -> begin
              begin if !Global.doubleCheck then
                FunTypeCheck.isState
                  (Obj.magic s : FunTypeCheck.StateSyn.state)
              else ()
              end;
              s
            end
          | InActive -> raise (Error "Not applicable: leftover constraints"))
        sl

    let menu
        (Operator ((S.State (n, (g, b), (ih, oh), d, o, h, f), i), sl, i_)
         as op) =
      let rec active (a, n) = match a with
        | [] -> n
        | InActive :: l -> active (l, n)
        | Active _ :: l -> active (l, n + 1)
      in
      let rec inactive (a, n) = match a with
        | [] -> n
        | InActive :: l -> inactive (l, n + 1)
        | Active _ :: l -> inactive (l, n)
      in
      let casesToString = function
        | 0 -> "zero cases"
        | 1 -> "1 case"
        | n -> Int.toString n ^ " cases"
      in
      let flagToString (n, m) = match m with
        | 0 -> ""
        | m ->
            (((" [active: " ^ Int.toString n) ^ " inactive: ") ^ Int.toString m)
            ^ "]"
      in
      (((("Splitting : " ^ Print.decToString g (I.ctxDec g i)) ^ " ")
       ^ H.indexToString i_)
      ^ flagToString (active (sl, 0), inactive (sl, 0)))
      ^ ""
  end

  (* recursive case *)
  (* non-recursive case *)
  (* aux (G, B) = L'

       Invariant:
       If   . |- G ctx
       and  G |- B tags
       then . |- L' = GxB lfctx
    *)
  (* conv ((G, s), (G', s')) = B

       Invariant:
       B iff G [s]  == G' [s']
       Might migrate in to conv module  --cs
    *)
  (* createEVarSpineW (G, (V, s)) = ((V', s') , S')

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
  (* s = id *)
  (* s = id *)
  (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
  (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
  (* someEVars (G, G1, s) = s'

       Invariant:
       If   |- G ctx
       and  G |- s : G'
       then G |- s' : G', G1

       Remark: This is someEVars from Recursion.fun with a generalized ih --cs
    *)
  (* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx
    *)
  (* constCases (G, (V, s), I, abstract, ops) = ops'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators from I
    *)
  (* paramCases (G, (V, s), k, abstract, ops) = ops'

       Invariant:
       If   G |- s : G'  G' |- V : type
       and  k a variable
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
         operators introduced by parameters <= k in G
    *)
  (* abstract state *)
  (* lowerSplitDest (G, k, (V, s'), abstract) = ops'

       Invariant:
       If  G0, G |- s' : G1  G1 |- V: type
       and  k = |local parameters in G|
       and  G is the context of local parameters
       and  abstract abstraction function
       then ops' is a list of all operators unifying with V[s']
            (it contains constant and parameter cases)
    *)
  (* split (x:D, sc, B, abstract) = cases'

       Invariant :
       If   |- G ctx
       and  G |- B tags
       and  G |- D : L
       then sc is a function, which maps
                Gp, Bp          (. |- Gp ctx   Gp |- Bp tags)
            to (G', B'), s', (G, B), p'
                              (. |- G' = Gp, G'' ctx
                               G'' contains only parameter declarations from G
                               G' |- B' tags
                               G' |- s' : G
                               and p' holds iff (G', B') contains a parameter
                             block independent of Gp, Bp)
        and  abstract is an abstraction function which maps
               (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G)
            to S'            (|- S' state)

       then cases' = (S1, ... Sn) are cases of the split
    *)
  (* |- G' = parameter blocks of G  ctx*)
  (* G' |- B' tags *)
  (* G' |- s' : G *)
  (* G' |- U' : V[s'] *)
  (* G' |- U'.s' : G, V[s'] *)
  (* . |- t : G1 *)
  (* . |- G2 [t] ctx *)
  (* G2 [t] |- B2 tags *)
  (* . |- G' ctx *)
  (* G' |- B' tags *)
  (* G' |- s : G = G0 *)
  (* G0 |- B0 tags *)
  (* abstract' U = S'

                   Invariant:
                   If   G' |- U' : V[s']
                   then |- S' state *)
  (* G' |- U' : V[s'] *)
  (* G' |- U.s' : G, V *)
  (* . |- t : G1 *)
  (* . |- G'' ctx *)
  (* G'' |- B'' tags *)
  (* G'' = G1'', G2', G2'' *)
  (* where G1'' |- G2' ctx, G2' is the abstracted parameter block *)
  (* occursInExp (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
  (* no case for Redex, EVar, EClo *)
  (* no case for FVar *)
  (* no case for SClo *)
  (* abstractInit S ((G', B'), s') = S'

       Invariant:
       If   |- S = (n, (G, B), (IH, OH), d, O, H, F) state
       and  |- G' ctx
       and  G' |- B' tags
       and  G' |- s' : G
       then |- S' = (n, (G', B'), (IH, OH), d, O[s'], H[s'], F[s']) state
    *)
  (* abstractCont ((x:V, t_), abstract) = abstract'

       Invariant:
       If   |- G ctx
       and  G |- V : type
       and  G |- B tags
       and  abstract is an abstraction function which maps
                    (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G, D)
                 to S'            (|- S' state)
       then abstract' is an abstraction function which maps
                    (Gn', Bn'), sn'  (|- Gn' ctx,  Gn' |- Bn' tags,  Gn' |- sn' : G)
                 to S'               (|- S' state)
    *)
  (* no other case should be possible by invariant *)
  (* expand' ((G, B), isIndex, abstract, makeAddress) = (sc', ops')

       Invariant:
       If   |- G ctx
       and  G |- B tags
       and  isIndex (k) = B function s.t. B holds iff k index
       and  abstract is an abstraction function which maps
               (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G)
            to S'            (|- S' state)
       and  makeAddress, a function which calculates the index of the variable
            to be split
       then sc' is a function, which maps
               Gp, Bp         (. |- Gp ctx   Gp |- Bp tags)
            to (G', B'), s', (G, B), p'
                              (. |- G' = Gp, G'' ctx
                               G'' contains only parameter declarations from G
                               G' |- B' tags
                               G' |- s' : G
                               and p' holds iff (G', B') contains a parameter
                             block independent of Gp, Bp)
       and  ops' is a list of splitting operators

       Optimization possible :
         instead of reconstructin (G, B) as the result of sc, just take (G, B)
    *)
  (* G' |- X : V[s'] *)
  (* G' |- X.s' : G, D *)
  (* no case of (I.Decl (G, D), I.Decl (G, S.Parameter NONE)) *)
  (* expand (S) = ops'

       Invariant:
       If   |- S state
       then ops' is a list of all possiblie splitting operators
    *)
  (* index (Op) = k

       Invariant:
       If   Op = (_, Sl)
       then k = |Sl|
    *)
  (* isInActive (F) = B

       Invariant:
       B holds iff F is inactive
    *)
  (* applicable (Op) = B'

       Invariant:
       If   Op = (_, Sl)
       then B' holds iff Sl does not contain inactive states
    *)
  (* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl)
       then Sl' = Sl

       Side effect: If Sl contains inactive states, an exception is raised
    *)
  (* menu (Op) = s'

       Invariant:
       If   Op = ((S, i), Sl)  and  S is named
       then s' is a string describing the operation in plain text

       (menu should hence be only called on operators which have
        been calculated from a named state)
    *)
  let expand = expand
  let menu = menu
  let applicable = applicable
  let apply = apply
  let index = index
  let compare = compare
end
(*! sharing Unify.IntSyn = IntSyn !*)
(*! structure CsManager : CS_MANAGER !*)
(*! sharing CsManager.IntSyn = IntSyn  !*)
(* local *)
(* functor Splitting *)

(* # 1 "src/meta/MtpSplitting.sml.ml" *)
