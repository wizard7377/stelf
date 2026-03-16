(* # 1 "src/meta/splitting.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open Mtp_global
open Mtp_abstract
open Mtp_print
open Funtypecheck

(* Splitting : Version 1.3 *)
(* Author: Carsten Schuermann *)
module type MTPSPLITTING = sig
  module StateSyn : STATESYN

  exception Error of string

  type nonrec operator

  val expand : StateSyn.state -> operator list
  val applicable : operator -> bool
  val apply : operator -> StateSyn.state list
  val menu : operator -> string
  val index : operator -> int
  val compare : operator * operator -> order
end
(* signature MTPSPLITTING *)

(* # 1 "src/meta/splitting.fun.ml" *)
open! Print
open! Global
open! Basis

(* Splitting : Version 1.3 *)
(* Author: Carsten Schuermann *)
module MTPSplitting (MTPSplitting__0 : sig
  module MTPGlobal : MTPGLOBAL
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn !*)
  module StateSyn' : STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn !*)
  (*! sharing StateSyn'.IntSyn = IntSyn !*)
  module Heuristic : HEURISTIC
  module MTPAbstract : MTPABSTRACT

  (*! sharing MTPAbstract.IntSyn = IntSyn !*)
  module MTPrint : MTPRINT
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
  module Subordinate : SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn !*)
  module FunTypeCheck : FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module Unify : UNIFY
end) : MTPSPLITTING = struct
  open MTPSplitting__0
  module StateSyn = StateSyn'

  exception Error of string

  (* Invariant:
     Case analysis generates a list of successor states
     (the cases) from a given state.

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

    let rec makeOperator = function
      | (s_, k), l_, S.Splits n, g, i_, m, true ->
          Operator
            ( (s_, k),
              l_,
              { sd = n; ind = i_; c = List.length l_; m; r = 1; p = g + 1 } )
      | (s_, k), l_, S.Splits n, g, i_, m, false ->
          Operator
            ( (s_, k),
              l_,
              { sd = n; ind = i_; c = List.length l_; m; r = 0; p = g + 1 } )

    let rec aux = function
      | I.Null, I.Null -> I.null_
      | I.Decl (g_, d_), I.Decl (b_, S.Lemma _) ->
          I.Decl (aux (g_, b_), F.Prim d_)
      | (I.Decl (_, d_) as g_), (I.Decl (_, S.Parameter (Some l)) as b_) ->
          let (F.LabelDec (name, _, g2_)) = F.labelLookup l in
          let psi'_, g'_ = aux' (g_, b_, List.length g2_) in
          I.Decl (psi'_, F.Block (F.CtxBlock (Some l, g'_)))

    and aux' = function
      | g_, b_, 0 -> (aux (g_, b_), I.null_)
      | I.Decl (g_, d_), I.Decl (b_, S.Parameter (Some _)), n ->
          let psi'_, g'_ = aux' (g_, b_, n - 1) in
          (psi'_, I.Decl (g'_, d_))

    let rec conv (gs_, gs'_) =
      let exception Conv in
      let rec conv = function
        | (I.Null, s), (I.Null, s') -> (s, s')
        | (I.Decl (g_, I.Dec (_, v_)), s), (I.Decl (g'_, I.Dec (_, v'_)), s') ->
            let s1, s1' = conv ((g_, s), (g'_, s')) in
            let ((s2, s2') as ps) = (I.dot1 s1, I.dot1 s1') in
            begin if Conv.conv ((v_, s1), (v'_, s1')) then ps else raise Conv
            end
        | _ -> raise Conv
      in
      try
        begin
          ignore (conv (gs_, gs'_));
          true
        end
      with Conv -> false

    let rec createEVarSpine (g_, vs_) = createEVarSpineW (g_, Whnf.whnf vs_)

    and createEVarSpineW = function
      | g_, ((I.Uni type_, s) as vs_) -> (I.Nil, vs_)
      | g_, ((I.Root _, s) as vs_) -> (I.Nil, vs_)
      | g_, (I.Pi (((I.Dec (_, v1_) as d_), _), v2_), s) ->
          let x_ = I.newEVar (g_, I.EClo (v1_, s)) in
          let s_, vs_ = createEVarSpine (g_, (v2_, I.Dot (I.Exp x_, s))) in
          (I.App (x_, s_), vs_)

    let rec createAtomConst (g_, h_) =
      let cid =
        begin match h_ with I.Const cid -> cid | I.Skonst cid -> cid
        end
      in
      let v_ = I.constType cid in
      let s_, vs_ = createEVarSpine (g_, (v_, I.id)) in
      (I.Root (h_, s_), vs_)

    let rec createAtomBVar (g_, k) =
      let (I.Dec (_, v_)) = I.ctxDec (g_, k) in
      let s_, vs_ = createEVarSpine (g_, (v_, I.id)) in
      (I.Root (I.BVar k, s_), vs_)

    let rec someEVars = function
      | g_, [], s -> s
      | g_, I.Dec (_, v_) :: l_, s ->
          someEVars (g_, l_, I.Dot (I.Exp (I.newEVar (g_, I.EClo (v_, s))), s))

    let rec maxNumberParams a =
      let rec maxNumberParams' n =
        begin if n < 0 then 0
        else
          let (F.LabelDec (name, g1_, g2_)) = F.labelLookup n in
          let m' =
            foldr
              (function
                | I.Dec (_, v_), m -> begin
                    if I.targetFam v_ = a then m + 1 else m
                  end)
              0 g2_
          in
          maxNumberParams' (n - 1) + m'
        end
      in
      maxNumberParams' (F.labelSize () - 1)

    let rec maxNumberLocalParams = function
      | I.Pi ((I.Dec (_, v1_), _), v2_), a ->
          let m = maxNumberLocalParams (v2_, a) in
          begin if I.targetFam v1_ = a then m + 1 else m
          end
      | I.Root _, a -> 0

    let rec maxNumberConstCases a = List.length (Index.lookup a)

    let rec maxNumberCases (v_, a) =
      maxNumberParams a + maxNumberLocalParams (v_, a) + maxNumberConstCases a

    let rec ctxSub = function
      | [], s -> []
      | d_ :: g_, s -> I.decSub (d_, s) :: ctxSub (g_, I.dot1 s)

    let rec createTags = function
      | 0, l -> I.null_
      | n, l -> I.Decl (createTags (n - 1, l), S.Parameter (Some l))

    let rec createLemmaTags = function
      | null_ -> I.null_
      | I.Decl (g_, d_) ->
          I.Decl (createLemmaTags g_, S.Lemma (S.Splits !MTPGlobal.maxSplit))

    let rec constCases = function
      | g_, vs_, [], abstract, ops -> ops
      | g_, vs_, I.Const c :: sgn_, abstract, ops ->
          let u_, vs'_ = createAtomConst (g_, I.Const c) in
          constCases
            ( g_,
              vs_,
              sgn_,
              abstract,
              Cs_manager.trail (function () ->
                  (try
                     begin if Unify.unifiable (g_, vs_, vs'_) then
                       Active (abstract u_) :: ops
                     else ops
                     end
                   with MTPAbstract.Error _ -> InActive :: ops)) )

    let rec paramCases = function
      | g_, vs_, 0, abstract, ops -> ops
      | g_, vs_, k, abstract, ops ->
          let u_, vs'_ = createAtomBVar (g_, k) in
          paramCases
            ( g_,
              vs_,
              k - 1,
              abstract,
              Cs_manager.trail (function () ->
                  (try
                     begin if Unify.unifiable (g_, vs_, vs'_) then
                       Active (abstract u_) :: ops
                     else ops
                     end
                   with MTPAbstract.Error _ -> InActive :: ops)) )

    let rec constAndParamCases ops0 (c, g_, k, (v_, s'), abstract) =
      constCases
        ( g_,
          (v_, s'),
          Index.lookup c,
          abstract,
          paramCases (g_, (v_, s'), k, abstract, ops0) )

    let rec metaCases (d, ops0) (c, g_, k, vs_, abstract) =
      let g = I.ctxLength g_ in
      let rec select = function
        | 0, ops -> ops
        | d', ops ->
            let n = g - d' + 1 in
            let (I.Dec (_, v_)) = I.ctxDec (g_, n) in
            let ops' =
              begin if I.targetFam v_ = c then
                let u_, vs'_ = createAtomBVar (g_, n) in
                Cs_manager.trail (function () ->
                    (try
                       begin if Unify.unifiable (g_, vs_, vs'_) then
                         Active (abstract u_) :: ops
                       else ops
                       end
                     with MTPAbstract.Error _ -> InActive :: ops))
              else ops
              end
            in
            select (d' - 1, ops')
      in
      select (d, ops0)

    let rec lowerSplitDest = function
      | g_, k, ((I.Root (I.Const c, _) as v_), s'), abstract, cases ->
          cases (c, g_, I.ctxLength g_, (v_, s'), abstract)
      | g_, k, (I.Pi ((d_, p_), v_), s'), abstract, cases ->
          let d'_ = I.decSub (d_, s') in
          lowerSplitDest
            ( I.Decl (g_, d'_),
              k + 1,
              (v_, I.dot1 s'),
              (fun u_ -> abstract (I.Lam (d'_, u_))),
              cases )

    let rec abstractErrorLeft ((g_, b_), s) =
      raise (MTPAbstract.Error "Cannot split left of parameters")

    let rec abstractErrorRight ((g_, b_), s) =
      raise (MTPAbstract.Error "Cannot split right of parameters")

    let rec split (((I.Dec (_, v_) as d_), t_), sc, abstract) =
      let rec split' (n, cases) =
        begin if n < 0 then
          let (g'_, b'_), s', (g0_, b0_), _ = sc (I.null_, I.null_) in
          let rec abstract' u'_ =
            let ((g''_, b''_), s'') : (I.dctx * S.tag I.ctx) * I.sub =
              Obj.magic
                (MTPAbstract.abstractSub'
                   ((g'_, b'_), I.Dot (I.Exp u'_, s'), I.Decl (b0_, t_)))
            in
            let _ =
              begin if !Global.doubleCheck then
                let psi''_ = aux (g''_, b''_) in
                let _ = TypeCheck.typeCheckCtx (F.makectx psi''_) in
                let psi_ =
                  aux (Obj.magic (I.Decl (g0_, d_), I.Decl (b0_, t_)))
                in
                let _ = TypeCheck.typeCheckCtx (F.makectx psi_) in
                FunTypeCheck.checkSub (psi''_, s'', psi_)
              else ()
              end
            in
            abstract ((g''_, b''_), s'')
          in
          lowerSplitDest (g'_, 0, (v_, s'), abstract', constAndParamCases cases)
        else
          let (F.LabelDec (name, g1_, g2_)) = F.labelLookup n in
          let t = someEVars (I.null_, g1_, I.id) in
          let b1_ = createLemmaTags (F.listToCtx g1_) in
          let g2t_ = ctxSub (g2_, t) in
          let length = List.length g2_ in
          let b2_ = createTags (length, n) in
          let (g'_, b'_), s', (g0_, b0_), p =
            sc (Names.ctxName (F.listToCtx g2t_), b2_)
          in
          let rec abstract' u'_ =
            begin if p then
              raise (MTPAbstract.Error "Cannot split right of parameters")
            else
              let ((g''_, b''_), s'') : (I.dctx * S.tag I.ctx) * I.sub =
                Obj.magic
                  ((Obj.magic MTPAbstract.abstractSub)
                     ( t,
                       b1_,
                       (g'_, b'_),
                       I.Dot (I.Exp u'_, s'),
                       I.Decl (b0_, t_) ))
              in
              let _ =
                begin if !Global.doubleCheck then
                  let psi''_ = aux (g''_, b''_) in
                  let _ = TypeCheck.typeCheckCtx (F.makectx psi''_) in
                  let psi_ =
                    aux (Obj.magic (I.Decl (g0_, d_), I.Decl (b0_, t_)))
                  in
                  let _ = TypeCheck.typeCheckCtx (F.makectx psi_) in
                  FunTypeCheck.checkSub (psi''_, s'', psi_)
                else ()
                end
              in
              abstract ((g''_, b''_), s'')
            end
          in
          let cases' =
            lowerSplitDest
              (g'_, 0, (v_, s'), abstract', metaCases (length, cases))
          in
          split' (n - 1, cases')
        end
      in
      split' (F.labelSize () - 1, [])

    let rec occursInExp = function
      | k, I.Uni _ -> false
      | k, I.Pi (dp_, v_) -> occursInDecP (k, dp_) || occursInExp (k + 1, v_)
      | k, I.Root (c_, s_) -> occursInCon (k, c_) || occursInSpine (k, s_)
      | k, I.Lam (d_, v_) -> occursInDec (k, d_) || occursInExp (k + 1, v_)
      | k, I.FgnExp (csid_, csfe) ->
          I.FgnExpStd.fold (csid_, csfe)
            (function
              | u_, b_ -> b_ || occursInExp (k, Whnf.normalize (u_, I.id)))
            false

    and occursInCon = function
      | k, I.BVar k' -> k = k'
      | k, I.Const _ -> false
      | k, I.Def _ -> false
      | k, I.Skonst _ -> false

    and occursInSpine = function
      | _, nil_ -> false
      | k, I.App (u_, s_) -> occursInExp (k, u_) || occursInSpine (k, s_)

    and occursInDec (k, I.Dec (_, v_)) = occursInExp (k, v_)
    and occursInDecP (k, (d_, _)) = occursInDec (k, d_)

    let rec isIndexInit k = false
    let rec isIndexSucc (d_, isIndex) k = occursInDec (k, d_) || isIndex (k + 1)
    let rec isIndexFail (d_, isIndex) k = isIndex (k + 1)

    let rec abstractInit
        (S.State (n, (g_, b_), (ih_, oh_), d, o_, h_, f_) as s_) ((g'_, b'_), s')
        =
      begin
        begin if !Global.doubleCheck then TypeCheck.typeCheckCtx g'_ else ()
        end;
        begin
          begin if !Global.doubleCheck then
            FunTypeCheck.isFor (g'_, F.forSub (f_, s'))
          else ()
          end;
          S.State
            ( n,
              (g'_, b'_),
              (ih_, oh_),
              d,
              S.orderSub (o_, s'),
              map (function i, f'_ -> (i, F.forSub (f'_, s'))) h_,
              F.forSub (f_, s') )
        end
      end

    let rec abstractCont ((d_, t_), abstract) ((g_, b_), s) =
      abstract
        ( ( I.Decl (g_, Whnf.normalizeDec (d_, s)),
            I.Decl (b_, S.normalizeTag (t_, s)) ),
          I.dot1 s )

    let rec makeAddressInit s_ k = (s_, k)
    let rec makeAddressCont makeAddress k = makeAddress (k + 1)

    let rec occursInOrder = function
      | n, S.Arg (us_, vt_), k, sc ->
          let u'_ = Whnf.normalize us_ in
          begin if occursInExp (k, u'_) then Some n else sc (n + 1)
          end
      | n, S.Lex os_, k, sc -> occursInOrders (n, os_, k, sc)
      | n, S.Simul os_, k, sc -> occursInOrders (n, os_, k, sc)

    and occursInOrders = function
      | n, [], k, sc -> sc n
      | n, o_ :: os_, k, sc ->
          occursInOrder
            (n, o_, k, function n' -> occursInOrders (n', os_, k, sc))

    let rec inductionInit o_ k = occursInOrder (0, o_, k, function n -> None)
    let rec inductionCont induction k = induction (k + 1)

    let rec expand' = function
      | ((I.Null, I.Null) as gb_), isIndex, abstract, makeAddress, induction ->
          ( (fun (gp_, bp_) ->
              ((gp_, bp_), I.Shift (I.ctxLength gp_), gb_, false)),
            [] )
      | ( ((I.Decl (g_, d_), I.Decl (b_, (S.Lemma (S.Splits _ as k_) as t_))) as
           gb_),
          isIndex,
          abstract,
          makeAddress,
          induction ) ->
          let sc, ops =
            expand'
              ( (g_, b_),
                isIndexSucc (d_, isIndex),
                abstractCont ((d_, t_), abstract),
                makeAddressCont makeAddress,
                inductionCont induction )
          in
          let (I.Dec (xOpt, v_)) = d_ in
          let rec sc' (gp_, bp_) =
            let (g'_, b'_), s', (g0_, b0_), p' = sc (gp_, bp_) in
            let x_ = I.newEVar (g'_, I.EClo (v_, s')) in
            ( (g'_, b'_),
              I.Dot (I.Exp x_, s'),
              (I.Decl (g0_, d_), I.Decl (b0_, t_)),
              p' )
          in
          let ops' =
            begin if (not (isIndex 1)) && S.splitDepth k_ > 0 then
              let a = I.targetFam v_ in
              makeOperator
                ( makeAddress 1,
                  split ((d_, Obj.magic t_), Obj.magic sc, abstract),
                  k_,
                  I.ctxLength g_,
                  induction 1,
                  maxNumberCases (v_, a),
                  Subordinate.below (a, a) )
              :: ops
            else ops
            end
          in
          (sc', ops')
      | ( (I.Decl (g_, d_), I.Decl (b_, (S.Lemma rl_ as t_))),
          isIndex,
          abstract,
          makeAddress,
          induction ) ->
          let sc, ops =
            expand'
              ( (g_, b_),
                isIndexSucc (d_, isIndex),
                abstractCont ((d_, t_), abstract),
                makeAddressCont makeAddress,
                inductionCont induction )
          in
          let (I.Dec (xOpt, v_)) = d_ in
          let rec sc' (gp_, bp_) =
            let (g'_, b'_), s', (g0_, b0_), p' = sc (gp_, bp_) in
            let x_ = I.newEVar (g'_, I.EClo (v_, s')) in
            ( (g'_, b'_),
              I.Dot (I.Exp x_, s'),
              (I.Decl (g0_, d_), I.Decl (b0_, t_)),
              p' )
          in
          (sc', ops)
      | ( (I.Decl (g_, d_), I.Decl (b_, (S.Lemma rLdone_ as t_))),
          isIndex,
          abstract,
          makeAddress,
          induction ) ->
          let sc, ops =
            expand'
              ( (g_, b_),
                isIndexSucc (d_, isIndex),
                abstractCont ((d_, t_), abstract),
                makeAddressCont makeAddress,
                inductionCont induction )
          in
          let (I.Dec (xOpt, v_)) = d_ in
          let rec sc' (gp_, bp_) =
            let (g'_, b'_), s', (g0_, b0_), p' = sc (gp_, bp_) in
            let x_ = I.newEVar (g'_, I.EClo (v_, s')) in
            ( (g'_, b'_),
              I.Dot (I.Exp x_, s'),
              (I.Decl (g0_, d_), I.Decl (b0_, t_)),
              p' )
          in
          (sc', ops)
      | ( (I.Decl (g_, d_), I.Decl (b_, (S.Parameter (Some _) as t_))),
          isIndex,
          abstract,
          makeAddress,
          induction ) ->
          let sc, ops =
            expand'
              ( (g_, b_),
                isIndexSucc (d_, isIndex),
                abstractErrorLeft,
                makeAddressCont makeAddress,
                inductionCont induction )
          in
          let (I.Dec (xOpt, v_)) = d_ in
          let rec sc' (gp_, bp_) =
            let (g'_, b'_), s', (g0_, b0_), _ = sc (gp_, bp_) in
            ( ( I.Decl (g'_, Names.decName (g'_, I.decSub (d_, s'))),
                I.Decl (b'_, t_) ),
              I.dot1 s',
              (I.Decl (g0_, d_), I.Decl (b0_, t_)),
              true )
          in
          (sc', ops)

    let rec expand (S.State (n, (g0_, b0_), _, _, o_, _, _) as s0_) =
      let _ =
        begin if !Global.doubleCheck then FunTypeCheck.isState (Obj.magic s0_)
        else ()
        end
      in
      let _, ops =
        expand'
          ( (g0_, b0_),
            isIndexInit,
            abstractInit s0_,
            makeAddressInit s0_,
            inductionInit o_ )
      in
      ops

    let rec index (Operator ((s_, index), sl_, { c = k })) = k

    let rec compare (Operator (_, _, i1_), Operator (_, _, i2_)) =
      H.compare (i1_, i2_)

    let rec isInActive = function Active _ -> false | InActive -> true

    let rec applicable (Operator (_, sl_, i_)) =
      not (List.exists isInActive sl_)

    let rec apply (Operator (_, sl_, i_)) =
      map
        (function
          | Active s_ -> begin
              begin if !Global.doubleCheck then
                FunTypeCheck.isState
                  (Obj.magic s_ : FunTypeCheck.StateSyn.state)
              else ()
              end;
              s_
            end
          | InActive -> raise (Error "Not applicable: leftover constraints"))
        sl_

    let rec menu
        (Operator
           ((S.State (n, (g_, b_), (ih_, oh_), d, o_, h_, f_), i), sl_, i_) as
         op_) =
      let rec active = function
        | [], n -> n
        | InActive :: l_, n -> active (l_, n)
        | Active _ :: l_, n -> active (l_, n + 1)
      in
      let rec inactive = function
        | [], n -> n
        | InActive :: l_, n -> inactive (l_, n + 1)
        | Active _ :: l_, n -> inactive (l_, n)
      in
      let rec casesToString = function
        | 0 -> "zero cases"
        | 1 -> "1 case"
        | n -> Int.toString n ^ " cases"
      in
      let rec flagToString = function
        | _, 0 -> ""
        | n, m ->
            (((" [active: " ^ Int.toString n) ^ " inactive: ") ^ Int.toString m)
            ^ "]"
      in
      (((("Splitting : " ^ Print.decToString (g_, I.ctxDec (g_, i))) ^ " ")
       ^ H.indexToString i_)
      ^ flagToString (active (sl_, 0), inactive (sl_, 0)))
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

       Remark: This is someEVars from recursion.fun with a generalized ih --cs
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
(*! structure Cs_manager : CS_MANAGER !*)
(*! sharing Cs_manager.IntSyn = IntSyn  !*)
(* local *)
(* functor Splitting *)

(* # 1 "src/meta/mtp_splitting.sml.ml" *)
