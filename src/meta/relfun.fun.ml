open! Weaken
open! Global
open! Basis

module RelFun (RelFun__0 : sig
  (* Converter from relational representation to a functional
   representation of proof terms *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure FunSyn' : FUNSYN !*)
  module ModeTable : MODETABLE

  (*! sharing ModeSyn.IntSyn = FunSyn'.IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = FunSyn'.IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = FunSyn'.IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = FunSyn'.IntSyn !*)
  module Weaken : WEAKEN

  (*! sharing Weaken.IntSyn = FunSyn'.IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = FunSyn'.IntSyn !*)
  module FunWeaken : FUNWEAKEN

  (*! sharing FunWeaken.FunSyn = FunSyn' !*)
  module FunNames : FUNNAMES
end) : RELFUN = struct
  (*! structure FunSyn = FunSyn' !*)
  exception Error of string

  open RelFun__0

  open! struct
    module F = FunSyn
    module I = IntSyn
    module M = ModeSyn

    let rec ctxSub = function
      | null_, s -> (I.null_, s)
      | I.Decl (g_, d_), s ->
          let g'_, s' = ctxSub (g_, s) in
          (I.Decl (g'_, I.decSub (d_, s')), I.dot1 s)

    let rec convertOneFor cid =
      let v_ =
        begin match I.sgnLookup cid with
        | I.ConDec (name, _, _, _, v_, kind_) -> v_
        | _ -> raise (Error "Type Constant declaration expected")
        end
      in
      let mS =
        begin match ModeTable.modeLookup cid with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS
        end
      in
      let rec convertFor' = function
        | I.Pi ((d_, _), v_), M.Mapp (M.Marg (plus_, _), mS), w1, w2, n ->
            let f'_, f''_ =
              convertFor' (v_, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n - 1)
            in
            ( (fun f_ -> F.All (F.Prim (Weaken.strengthenDec (d_, w1)), f'_ f_)),
              f''_ )
        | I.Pi ((d_, _), v_), M.Mapp (M.Marg (minus_, _), mS), w1, w2, n ->
            let f'_, f''_ =
              convertFor' (v_, mS, I.comp (w1, I.shift), I.dot1 w2, n + 1)
            in
            (f'_, F.Ex (I.decSub (d_, w2), f''_))
        | I.Uni type_, mnil_, _, _, _ -> ((fun f_ -> f_), F.True)
        | _ -> raise (Error "type family must be +/- moded")
      in
      let rec shiftPlus mS =
        let rec shiftPlus' = function
          | mnil_, n -> n
          | M.Mapp (M.Marg (plus_, _), mS'), n -> shiftPlus' (mS', n + 1)
          | M.Mapp (M.Marg (minus_, _), mS'), n -> shiftPlus' (mS', n)
        in
        shiftPlus' (mS, 0)
      in
      let n = shiftPlus mS in
      let f_, f'_ = convertFor' (v_, mS, I.id, I.Shift n, n) in
      f_ f'_

    let rec convertFor = function
      | [] -> raise (Error "Empty theorem")
      | a :: [] -> convertOneFor a
      | a :: l_ -> F.And (convertOneFor a, convertFor l_)

    let rec occursInExpN = function
      | k, I.Uni _ -> false
      | k, I.Pi (dp_, v_) -> occursInDecP (k, dp_) || occursInExpN (k + 1, v_)
      | k, I.Root (h_, s_) -> occursInHead (k, h_) || occursInSpine (k, s_)
      | k, I.Lam (d_, v_) -> occursInDec (k, d_) || occursInExpN (k + 1, v_)
      | k, I.FgnExp (csid_, csfe) ->
          I.FgnExpStd.fold (csid_, csfe)
            (function
              | u_, b_ -> b_ || occursInExpN (k, Whnf.normalize (u_, I.id)))
            false

    and occursInHead = function
      | k, I.BVar k' -> k = k'
      | k, I.Const _ -> false
      | k, I.Def _ -> false
      | k, I.FgnConst _ -> false

    and occursInSpine = function
      | _, nil_ -> false
      | k, I.App (u_, s_) -> occursInExpN (k, u_) || occursInSpine (k, s_)

    and occursInDec (k, I.Dec (_, v_)) = occursInExpN (k, v_)
    and occursInDecP (k, (d_, _)) = occursInDec (k, d_)
    and occursInExp (k, u_) = occursInExpN (k, Whnf.normalize (u_, I.id))

    let rec dot1inv w = Weaken.strengthenSub (I.comp (I.shift, w), I.shift)
    let rec shiftinv w = Weaken.strengthenSub (w, I.shift)
    let rec eqIdx = function I.Idx n, I.Idx k -> n = k | _ -> false

    let rec peel w =
      begin if eqIdx (I.bvarSub (1, w), I.Idx 1) then dot1inv w else shiftinv w
      end

    let rec peeln = function 0, w -> w | n, w -> peeln (n - 1, peel w)

    let rec domain = function
      | g_, I.Dot (I.Idx _, s) -> domain (g_, s) + 1
      | null_, I.Shift 0 -> 0
      | (I.Decl _ as g_), I.Shift 0 -> domain (g_, I.Dot (I.Idx 1, I.Shift 1))
      | I.Decl (g_, _), I.Shift n -> domain (g_, I.Shift (n - 1))

    let rec strengthen (psi_, (a, s_), w, m) =
      let mS =
        begin match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS
        end
      in
      let rec args = function
        | nil_, mnil_ -> []
        | I.App (u_, s'_), M.Mapp (M.Marg (m', _), mS) ->
            let l_ = args (s'_, mS) in
            begin match M.modeEqual (m, m') with
            | true -> u_ :: l_
            | false -> l_
            end
      in
      let rec strengthenArgs = function
        | [], s -> []
        | u_ :: l_, s -> Weaken.strengthenExp (u_, s) :: strengthenArgs (l_, s)
      in
      let rec occursInArgs = function
        | n, [] -> false
        | n, u_ :: l_ -> occursInExp (n, u_) || occursInArgs (n, l_)
      in
      let rec occursInPsi = function
        | n, ([], l_) -> occursInArgs (n, l_)
        | n, (F.Prim (I.Dec (_, v_)) :: psi1_, l_) ->
            occursInExp (n, v_) || occursInPsi (n + 1, (psi1_, l_))
        | n, (F.Block (F.CtxBlock (l, g_)) :: psi1_, l_) ->
            occursInG (n, g_, function n' -> occursInPsi (n', (psi1_, l_)))
      and occursInG = function
        | n, null_, k -> k n
        | n, I.Decl (g_, I.Dec (_, v_)), k ->
            occursInG
              (n, g_, function n' -> occursInExp (n', v_) || k (n' + 1))
      in
      let rec occursBlock (g_, (psi2_, l_)) =
        let rec occursBlock = function
          | null_, n -> false
          | I.Decl (g_, d_), n ->
              occursInPsi (n, (psi2_, l_)) || occursBlock (g_, n + 1)
        in
        occursBlock (g_, 1)
      in
      let rec inBlock = function
        | null_, (bw, w1) -> (bw, w1)
        | I.Decl (g_, d_), (bw, w1) -> begin
            if eqIdx (I.bvarSub (1, w1), I.Idx 1) then
              inBlock (g_, (true, dot1inv w1))
            else inBlock (g_, (bw, Weaken.strengthenSub (w1, I.shift)))
          end
      in
      let rec blockSub = function
        | null_, w -> (I.null_, w)
        | I.Decl (g_, I.Dec (name, v_)), w ->
            let g'_, w' = blockSub (g_, w) in
            let v'_ = Weaken.strengthenExp (v_, w') in
            (I.Decl (g'_, I.Dec (name, v'_)), I.dot1 w')
      in
      let rec strengthen' = function
        | null_, psi2_, l_, w1 -> (I.null_, I.id)
        | I.Decl (psi1_, (F.Prim (I.Dec (name, v_)) as ld_)), psi2_, l_, w1 ->
            let bw, w1' =
              begin if eqIdx (I.bvarSub (1, w1), I.Idx 1) then (true, dot1inv w1)
              else (false, Weaken.strengthenSub (w1, I.shift))
              end
            in
            begin if bw || occursInPsi (1, (psi2_, l_)) then
              let psi1'_, w' = strengthen' (psi1_, ld_ :: psi2_, l_, w1') in
              let v'_ = Weaken.strengthenExp (v_, w') in
              (I.Decl (psi1'_, F.Prim (I.Dec (name, v'_))), I.dot1 w')
            else
              let w2 = I.shift in
              let psi2'_, w2' = FunWeaken.strengthenPsi' (psi2_, w2) in
              let l'_ = strengthenArgs (l_, w2') in
              let psi1''_, w' = strengthen' (psi1_, psi2'_, l'_, w1') in
              (psi1''_, I.comp (w', I.shift))
            end
        | ( I.Decl (psi1_, (F.Block (F.CtxBlock (name, g_)) as ld_)),
            psi2_,
            l_,
            w1 ) ->
            let bw, w1' = inBlock (g_, (false, w1)) in
            begin if bw || occursBlock (g_, (psi2_, l_)) then
              let psi1'_, w' = strengthen' (psi1_, ld_ :: psi2_, l_, w1') in
              let g''_, w'' = blockSub (g_, w') in
              (I.Decl (psi1'_, F.Block (F.CtxBlock (name, g''_))), w'')
            else
              let w2 = I.Shift (I.ctxLength g_) in
              let psi2'_, w2' = FunWeaken.strengthenPsi' (psi2_, w2) in
              let l'_ = strengthenArgs (l_, w2') in
              strengthen' (psi1_, psi2'_, l'_, w1')
            end
      in
      strengthen' (psi_, [], args (s_, mS), w)

    let rec recursion l_ =
      let f_ = convertFor l_ in
      let rec name = function
        | a :: [] -> I.conDecName (I.sgnLookup a)
        | a :: l_ -> (I.conDecName (I.sgnLookup a) ^ "/") ^ name l_
      in
      function p -> F.Rec (F.MDec (Some (name l_), f_), p)

    let rec abstract a =
      let mS =
        begin match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS
        end
      in
      let v_ =
        begin match I.sgnLookup a with
        | I.ConDec (name, _, _, _, v_, kind_) -> v_
        | _ -> raise (Error "Type Constant declaration expected")
        end
      in
      let rec abstract' = function
        | (_, mnil_), w -> fun p -> p
        | (I.Pi ((d_, _), v2_), M.Mapp (M.Marg (plus_, _), mS)), w ->
            let d'_ = Weaken.strengthenDec (d_, w) in
            let p_ = abstract' ((v2_, mS), I.dot1 w) in
            fun p -> F.Lam (F.Prim d'_, p_ p)
        | (I.Pi (_, v2_), M.Mapp (M.Marg (minus_, _), mS)), w ->
            abstract' ((v2_, mS), I.comp (w, I.shift))
      in
      abstract' ((v_, mS), I.id)

    let rec transformInit (psi_, (a, s_), w1) =
      let mS =
        begin match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS
        end
      in
      let v_ =
        begin match I.sgnLookup a with
        | I.ConDec (name, _, _, _, v_, kind_) -> v_
        | _ -> raise (Error "Type Constant declaration expected")
        end
      in
      let rec transformInit' = function
        | (nil_, mnil_), I.Uni type_, (w, s) -> (w, s)
        | ( (I.App (u_, s_), M.Mapp (M.Marg (minus_, _), mS)),
            I.Pi (_, v2_),
            (w, s) ) ->
            let w' = I.comp (w, I.shift) in
            let s' = s in
            transformInit' ((s_, mS), v2_, (w', s'))
        | ( (I.App (u_, s_), M.Mapp (M.Marg (plus_, _), mS)),
            I.Pi ((I.Dec (name, v1_), _), v2_),
            (w, s) ) ->
            let v1'_ = Weaken.strengthenExp (v1_, w) in
            let w' = I.dot1 w in
            let u'_ = Weaken.strengthenExp (u_, w1) in
            let s' = Whnf.dotEta (I.Exp u'_, s) in
            transformInit' ((s_, mS), v2_, (w', s'))
      in
      transformInit' ((s_, mS), v_, (I.id, I.Shift (F.lfctxLength psi_)))

    let rec transformDec (ts_, (psi_, g0_), d, (a, s_), w1, w2, t0) =
      let mS =
        begin match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS
        end
      in
      let v_ =
        begin match I.sgnLookup a with
        | I.ConDec (name, _, _, _, v_, kind_) -> v_
        | _ -> raise (Error "Type Constant declaration expected")
        end
      in
      let rec raiseExp (g_, u_, a) =
        let rec raiseExp' = function
          | null_ -> (I.id, function x -> x)
          | I.Decl (g_, (I.Dec (_, v_) as d_)) ->
              let w, k = raiseExp' g_ in
              begin if Subordinate.belowEq (I.targetFam v_, a) then
                ( I.dot1 w,
                  function x -> k (I.Lam (Weaken.strengthenDec (d_, w), x)) )
              else (I.comp (w, I.shift), k)
              end
        in
        let w, k = raiseExp' g_ in
        k (Weaken.strengthenExp (u_, w))
      in
      let rec raiseType (g_, u_, a) =
        let rec raiseType' = function
          | null_, n -> (I.id, (function x -> x), function s_ -> s_)
          | I.Decl (g_, (I.Dec (_, v_) as d_)), n ->
              let w, k, k' = raiseType' (g_, n + 1) in
              begin if Subordinate.belowEq (I.targetFam v_, a) then
                ( I.dot1 w,
                  (function
                  | x -> k (I.Pi ((Weaken.strengthenDec (d_, w), I.Maybe), x))),
                  function s_ -> I.App (I.Root (I.BVar n, I.Nil), s_) )
              else (I.comp (w, I.shift), k, k')
              end
        in
        let w, k, k' = raiseType' (g_, 2) in
        (k (Weaken.strengthenExp (u_, w)), I.Root (I.BVar 1, k' I.Nil))
      in
      let rec exchangeSub g0_ =
        let g0 = I.ctxLength g0_ in
        let rec exchangeSub' = function
          | 0, s -> s
          | k, s -> exchangeSub' (k - 1, I.Dot (I.Idx k, s))
        in
        I.Dot (I.Idx (g0 + 1), exchangeSub' (g0, I.Shift (g0 + 1)))
      in
      let rec transformDec' = function
        | d, (nil_, mnil_), I.Uni type_, (z1, z2), (w, t) ->
            (w, t, (d, (fun (k, ds_) -> ds_ k), fun _ -> F.Empty))
        | ( d,
            (I.App (u_, s_), M.Mapp (M.Marg (minus_, _), mS)),
            I.Pi ((I.Dec (_, v1_), dp_), v2_),
            (z1, z2),
            (w, t) ) ->
            let g = I.ctxLength g0_ in
            let w1' = peeln (g, w1) in
            let g1_, _ = Weaken.strengthenCtx (g0_, w1') in
            let g2_, _ = ctxSub (g1_, z1) in
            let v1''_, ur_ =
              raiseType (g2_, I.EClo (v1_, z2), I.targetFam v1_)
            in
            let w' =
              begin match dp_ with
              | maybe_ -> I.dot1 w
              | no_ -> I.comp (w, I.shift)
              end
            in
            let u0_ = raiseExp (g0_, u_, I.targetFam v1''_) in
            let u'_ = Weaken.strengthenExp (u0_, w2) in
            let t' = Whnf.dotEta (I.Exp u'_, t) in
            let z1' = I.comp (z1, I.shift) in
            let xc = exchangeSub g0_ in
            let z2n = I.comp (z2, I.comp (I.shift, xc)) in
            let ur'_ = I.EClo (ur_, xc) in
            let z2' = Whnf.dotEta (I.Exp ur'_, z2n) in
            let w'', t'', (d', dplus_, dminus_) =
              transformDec' (d + 1, (s_, mS), v2_, (z1', z2'), (w', t'))
            in
            (w'', t'', (d', dplus_, function k -> F.Split (k, dminus_ 1)))
        | ( d,
            (I.App (u_, s_), M.Mapp (M.Marg (plus_, _), mS)),
            I.Pi ((I.Dec (name, v1_), _), v2_),
            (z1, z2),
            (w, t) ) ->
            let v1'_ = Weaken.strengthenExp (v1_, w) in
            let w' = I.dot1 w in
            let u'_ = Weaken.strengthenExp (u_, w1) in
            let t' = t in
            let z1' = F.dot1n (g0_, z1) in
            let z2' = I.Dot (I.Exp (I.EClo (u'_, z1')), z2) in
            let w'', t'', (d', dplus_, dminus_) =
              transformDec' (d + 1, (s_, mS), v2_, (z1, z2'), (w', t'))
            in
            ( w'',
              t'',
              (d', (fun (k, ds_) -> F.App ((k, u'_), dplus_ (1, ds_))), dminus_)
            )
      in
      let w'', t'', (d', dplus_, dminus_) =
        transformDec'
          ( d,
            (s_, mS),
            v_,
            (I.id, I.Shift (domain (psi_, t0) + I.ctxLength g0_)),
            (I.id, t0) )
      in
      let rec varHead ts_ (w'', t'', (d', dplus_, dminus_)) =
        let rec head' = function
          | a' :: [], d1, k1 -> (d1, k1)
          | a' :: ts'_, d1, k1 -> begin
              if a = a' then (d1 + 1, function xx -> F.Left (xx, k1 1))
              else
                let d2, k2 = head' (ts'_, d1 + 1, k1) in
                (d2, function xx -> F.Right (xx, k2 1))
            end
        in
        let d2, k2 = head' (ts_, d', function xx -> dplus_ (xx, dminus_)) in
        (d2, w'', t'', k2 d)
      in
      let rec lemmaHead (w'', t'', (d', dplus_, dminus_)) =
        let name = I.conDecName (I.sgnLookup a) in
        let l =
          begin match FunNames.nameLookup name with
          | None -> raise (Error (("Lemma " ^ name) ^ " not defined"))
          | Some lemma -> lemma
          end
        in
        (d' + 1, w'', t'', F.Lemma (l, dplus_ (1, dminus_)))
      in
      begin if List.exists (function x -> x = a) ts_ then
        varHead ts_ (w'', t'', (d', dplus_, dminus_))
      else lemmaHead (w'', t'', (d', dplus_, dminus_))
      end

    let rec transformConc ((a, s_), w) =
      let mS =
        begin match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS
        end
      in
      let rec transformConc' = function
        | nil_, mnil_ -> F.Unit
        | I.App (u_, s'_), M.Mapp (M.Marg (plus_, _), mS') ->
            transformConc' (s'_, mS')
        | I.App (u_, s'_), M.Mapp (M.Marg (minus_, _), mS') ->
            F.Inx (Weaken.strengthenExp (u_, w), transformConc' (s'_, mS'))
      in
      transformConc' (s_, mS)

    let rec traverse (ts_, c) =
      let rec traverseNeg = function
        | c'', psi_, (I.Pi (((I.Dec (_, v1_) as d_), maybe_), v2_), v), l_ ->
          begin
            match
              traverseNeg
                ( c'',
                  I.Decl (psi_, F.Prim (Weaken.strengthenDec (d_, v))),
                  (v2_, I.dot1 v),
                  l_ )
            with
            | Some (w', d', pq'_), l'_ -> (Some (peel w', d', pq'_), l'_)
            | None, l'_ -> (None, l'_)
          end
        | c'', psi_, (I.Pi (((I.Dec (_, v1_) as d_), no_), v2_), v), l_ -> begin
            match traverseNeg (c'', psi_, (v2_, I.comp (v, I.shift)), l_) with
            | Some (w', d', pq'_), l'_ ->
                traversePos
                  ( c'',
                    psi_,
                    I.null_,
                    (Weaken.strengthenExp (v1_, v), I.id),
                    Some (w', d', pq'_),
                    l'_ )
            | None, l'_ ->
                traversePos
                  ( c'',
                    psi_,
                    I.null_,
                    (Weaken.strengthenExp (v1_, v), I.id),
                    None,
                    l'_ )
          end
        | c'', psi_, ((I.Root (I.Const c', s_) as v_), v), l_ -> begin
            if c = c' then
              let s'_ = Weaken.strengthenSpine (s_, v) in
              let psi'_, w' =
                strengthen
                  (psi_, (c', s'_), I.Shift (F.lfctxLength psi_), M.Plus)
              in
              let w'', s'' = transformInit (psi'_, (c', s'_), w') in
              ( Some
                  ( w',
                    1,
                    ( (fun p -> (psi'_, s'', p)),
                      fun wf -> transformConc ((c', s'_), wf) ) ),
                l_ )
            else (None, l_)
          end
      and traversePos = function
        | ( c'',
            psi_,
            g_,
            (I.Pi (((I.Dec (_, v1_) as d_), maybe_), v2_), v),
            Some (w, d, pq_),
            l_ ) -> begin
            match
              traversePos
                ( c'',
                  psi_,
                  I.Decl (g_, Weaken.strengthenDec (d_, v)),
                  (v2_, I.dot1 v),
                  Some (I.dot1 w, d, pq_),
                  l_ )
            with
            | Some (w', d', pq'_), l'_ -> (Some (w', d', pq'_), l'_)
          end
        | ( c'',
            psi_,
            g_,
            (I.Pi (((I.Dec (_, v1_) as d_), no_), v2_), v),
            Some (w, d, pq_),
            l_ ) -> begin
            match
              traversePos
                (c'', psi_, g_, (v2_, I.comp (v, I.shift)), Some (w, d, pq_), l_)
            with
            | Some (w', d', pq'_), l'_ -> begin
                match
                  traverseNeg
                    ( c'',
                      I.Decl (psi_, F.Block (F.CtxBlock (None, g_))),
                      (v1_, v),
                      l'_ )
                with
                | Some (w'', d'', (p''_, q''_)), l''_ ->
                    (Some (w', d', pq'_), p''_ (q''_ w'') :: l''_)
                | None, l''_ -> (Some (w', d', pq'_), l''_)
              end
          end
        | c'', psi_, null_, (v_, v), Some (w1, d, (p_, q_)), l_ ->
            let (I.Root (I.Const a', s_)) =
              Whnf.normalize (Weaken.strengthenExp (v_, v), I.id)
            in
            let psi'_, w2 = strengthen (psi_, (a', s_), w1, M.Minus) in
            let _ =
              begin if !Global.doubleCheck then
                TypeCheck.typeCheck
                  (F.makectx psi'_, (I.Uni I.Type, I.Uni I.Kind))
              else ()
              end
            in
            let w3 = Weaken.strengthenSub (w1, w2) in
            let d4, w4, t4, ds_ =
              transformDec (ts_, (psi'_, I.null_), d, (a', s_), w1, w2, w3)
            in
            ( Some
                ( w2,
                  d4,
                  ( (fun p ->
                      p_ (F.Let (ds_, F.Case (F.Opts [ (psi'_, t4, p) ])))),
                    q_ ) ),
              l_ )
        | c'', psi_, g_, (v_, v), Some (w1, d, (p_, q_)), l_ ->
            let (I.Root (I.Const a', s_)) = Weaken.strengthenExp (v_, v) in
            let (I.Decl (psi'_, F.Block (F.CtxBlock (name, g2_))) as dummy), w2
                =
              strengthen
                ( I.Decl (psi_, F.Block (F.CtxBlock (None, g_))),
                  (a', s_),
                  w1,
                  M.Minus )
            in
            let _ =
              begin if !Global.doubleCheck then
                TypeCheck.typeCheck
                  (F.makectx dummy, (I.Uni I.Type, I.Uni I.Kind))
              else ()
              end
            in
            let g = I.ctxLength g_ in
            let w1' = peeln (g, w1) in
            let w2' = peeln (g, w2) in
            let g1_, _ = Weaken.strengthenCtx (g_, w1') in
            let w3 = Weaken.strengthenSub (w1', w2') in
            let d4, w4, t4, ds_ =
              transformDec (ts_, (psi'_, g_), d, (a', s_), w1, w2', w3)
            in
            ( Some
                ( w2',
                  d4,
                  ( (fun p ->
                      p_
                        (F.Let
                           ( F.New (F.CtxBlock (None, g1_), ds_),
                             F.Case (F.Opts [ (psi'_, t4, p) ]) ))),
                    q_ ) ),
              l_ )
        | ( c'',
            psi_,
            g_,
            (I.Pi (((I.Dec (_, v1_) as d_), maybe_), v2_), v),
            None,
            l_ ) ->
            traversePos
              ( c'',
                psi_,
                I.Decl (g_, Weaken.strengthenDec (d_, v)),
                (v2_, I.dot1 v),
                None,
                l_ )
        | ( c'',
            psi_,
            g_,
            (I.Pi (((I.Dec (_, v1_) as d_), no_), v2_), v),
            None,
            l_ ) -> begin
            match
              traversePos (c'', psi_, g_, (v2_, I.comp (v, I.shift)), None, l_)
            with
            | None, l'_ -> begin
                match
                  traverseNeg
                    ( c'',
                      I.Decl (psi_, F.Block (F.CtxBlock (None, g_))),
                      (v1_, v),
                      l'_ )
                with
                | Some (w'', d'', (p''_, q''_)), l''_ ->
                    (None, p''_ (q''_ w'') :: l''_)
                | None, l''_ -> (None, l''_)
              end
          end
        | c'', psi_, g_, (v_, v), None, l_ -> (None, l_)
      in
      let rec traverseSig' (c'', l_) =
        begin if c'' = (fun (r, _) -> r) (I.sgnSize ()) then l_
        else begin
          match I.sgnLookup c'' with
          | I.ConDec (name, _, _, _, v_, type_) -> begin
              match traverseNeg (c'', I.null_, (v_, I.id), l_) with
              | Some (wf, d', (p'_, q'_)), l'_ ->
                  traverseSig' (c'' + 1, p'_ (q'_ wf) :: l'_)
              | None, l'_ -> traverseSig' (c'' + 1, l'_)
            end
          | _ -> traverseSig' (c'' + 1, l_)
        end
        end
      in
      traverseSig' (0, [])

    let rec convertPro ts_ =
      let rec convertOnePro a =
        let v_ =
          begin match I.sgnLookup a with
          | I.ConDec (name, _, _, _, v_, kind_) -> v_
          | _ -> raise (Error "Type Constant declaration expected")
          end
        in
        let mS =
          begin match ModeTable.modeLookup a with
          | None -> raise (Error "Mode declaration expected")
          | Some mS -> mS
          end
        in
        let p_ = abstract a in
        p_ (F.Case (F.Opts (traverse (ts_, a))))
      in
      let rec convertPro' = function
        | [] -> raise (Error "Cannot convert Empty program")
        | a :: [] -> convertOnePro a
        | a :: ts'_ -> F.Pair (convertOnePro a, convertPro' ts'_)
      in
      let r_ = recursion ts_ in
      r_ (convertPro' ts_)
  end

  (* ctxSub (G, s) = (G', s')

       Invariant:
       if   Psi |- G ctx
       and  Psi' |- s : Psi
       then Psi' |- G' ctx
       and  Psi', G' |- s' : G
       and  G' = G [s],  declarationwise defined
    *)
  (* convertFor' (V, mS, w1, w2, n) = (F', F'')

           Invariant:
           If   G |- V = {{G'}} type :kind
           and  G |- w1 : G+
           and  G+, G'+, G- |- w2 : G
           and  G+, G'+, G- |- ^n : G+
           and  mS is a spine for G'
           then F'  is a formula excepting a another formula as argument s.t.
                If G+, G'+ |- F formula,
                then . |- F' F formula
           and  G+, G'+ |- F'' formula
        *)
  (* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)
  (* convertFor L = F'

       Invariant:
       If   L is a list of type families
       then F' is the conjunction of the logical interpretation of each
            type family
     *)
  (* occursInExpN (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
  (* no case for Redex, EVar, EClo *)
  (* no case for FVar *)
  (* no case for SClo *)
  (* dot1inv w = w'

       Invariant:
       If   G, A |- w : G', A
       then G |- w' : G'
       and  w = 1.w' o ^
    *)
  (* shiftinv (w) = w'

       Invariant:
       If   G, A |- w : G'
       and  1 does not occur in w
       then w  = w' o ^
    *)
  (* domain (G2, w) = n'

       Invariant:
       If   G2 |- w: G1   and w weakening substitution
       then n' = |G1|
    *)
  (* strenghten (Psi, (a, S), w, m) = (Psi', w')

       Invariant:
       If   |- Psi ctx
       and  |- Psi1 ctx      where Psi1 is a subcontext of Psi
       and  |- Psi2 ctx
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} > type
       and  Psi |- w : Psi1
       and  m mode
       then |- Psi' ctx
       and  Psi |- w' : Psi'
       where Psi' extends Psi1
    *)
  (* testBlock (G, (bw, w1)) = (bw', w')

           Invariant:
           If   |- G ctx
           and  |- G1 ctx
           and  |- G2 ctx
           and  G1 |- w1 : G2, G
           and  bw is a boolean value
           then there ex. a G1'
           s.t. |- G1' ctx
           and  G1' |- w' : G2
           and  bw' = bw or (G1 =/= G1')
         *)
  (* strengthen' (Psi1, Psi2, S, w1) =  (Psi', w')

           Invariant:
           If   |- Psi1 ctx
           and  Psi1 |- Psi2 ctx      (Psi2 is a list to maintain order)
           and  |- Psi3 ctx
           and  Psi1 |- w1 : Psi3     where w1 is a weakening substitution
           and  Psi1, Psi2 |- S : V1 > V2
           then |- Psi' ctx
           and  Psi1 |- w' : Psi'     where w' is a weakening substitution
           where Psi3 < Psi' < Psi1   (Psi' contains all variables of Psi3
                                       and all variables occuring in m
                                       position in S)
        *)
  (* =  I.id *)
  (* abstract a = P'

       Invariant:
       If   a is a type family
       and  Sigma (a) = {x1:A1}..{xn:An} type
       then for all P s.t.
            +x1:A1, .., +xn:An; . |- P in [[-x1:A1]] .. [[-xn:An]] true
            . ;. |- (P' P) in [[+x1:A1]] .. [[+xn:An]] [[-x1:A1]] .. [[-xn:An]] true
    *)
  (* abstract' ((V, mS), w) = P'

           Invariant:
           If  Sigma (a) = {x1:A1} .. {xn:An} type
           and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
           and  Gamma= x1:A1, .. x(j-1):A(j-1)
           and  Gamma |- w : Gamma+
           then P' is a Lam abstraction
        *)
  (* transformInit (Psi, (a, S), w1) = (w', s')

       Invariant:
       If   |- Psi ctx
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w1 : Psi+
       then |- Gamma+ ctx
       and  Gamma+ = +x(k1):A(k1), ... +x(km):A(km)
       and  Psi+ |- s' : Gamma+
       and  x1:A1 .. xn:An |- w: Gamma+    (w weakening substitution)
    *)
  (* transformInit' ((S, mS), V, (w, s)) = (w', s')

           Invariant:
           If   Psi |- S : V > type
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi |- w1 : Psi+
           and  Psi+ |- s : +x1:A1... +x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+ |- s' : +x1:A1 .. +xn:An
        *)
  (* transformDec (c'', (Psi+-, G0), d, (a, S), w1, w2, t) = (d', w', s', t', Ds)

       Invariant:
       If   |- Psi ctx
       and  Psi |- G0 ctx
       and  d = |Delta|
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi, G0 |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi, G0 |- w1 : Psi+, G0[w1^-1]
       and  Psi |- w2 : Psi+-
       and  Psi+- |- t0 : Psi+
       then |- Gamma+ ctx
       and  Gamma+ = +x(k1):A(k1), ... +x(km):A(km)
       and  Psi |- s' : Gamma+
       and  x1:A1 .. xn:An |- w': Gamma+    (w weakening substitution)
       and  Psi+- |- t' : Psi+, -x(k1):{G0} A(k1), ... -x(km):{G0} A(km)
       and  d' = |Delta'|
    *)
  (* raiseExp (G, U, a) = U'

           Invariant:
           If   |- Psi ctx         (for some given Psi)
           and  Psi |- G ctx
           and  Psi, G |- U : V    (for some V)
           then Psi, G |- [[G]] U : {{G}} V     (wrt subordination)
        *)
  (* raiseExp G = (w', k)

               Invariant:
               If   |-  Psi ctx
               and  Psi |- G ctx
               and  Psi |- G' ctx   which ARE subordinate to a
               then Psi, G |- w : Psi, G'
               and  k is a continuation calculuting the right exprssion:
                    for all U, s.t. Psi, G |- U : V
                    Psi |- [[G']] U : {{G'}} V
            *)
  (* raiseType (G, U, a) = U'

           Invariant:
           If   |- Psi ctx         (for some given Psi)
           and  Psi |- G ctx
           and  Psi, G |- U : V    (for some V)
           then Psi, G |- [[G]] U : {{G}} V     (wrt subordination)
           and  Psi, G, x:{{G}} V |- x G : V
        *)
  (* raiseType (G, n) = (w', k, S')

              Invariant:
              If   |-  Psi ctx
              and  Psi |- G, Gv ctx
              and  Psi |- G' ctx   which ARE subordinate to a
              and  n = |Gv| + 1
              then Psi, G |- w : Psi, G'
              and  k is a continuation calculating the right exprssion:
                   for all U, s.t. Psi, G |- U : V
                   Psi |- [[G']] U : {{G'}} V
              and  k' is a continuation calculating the corresponding spine:
                   for all S, s.t. Psi, G, G0,|- ... refine
            *)
  (* exchangeSub (G0) = s'

           Invariant:
           For some Psi, some G, some V:
           Psi, V, G0 |- s' : Psi, G0, V
        *)
  (* transformDec' (d, (S, mS), V, (z1, z2), (w, t)) = (d', w', t', (Ds+, Ds-))

           Invariant:
           If   Psi, G0 |- S : V > type
           and  S doesn't contain Skolem constants
           and  d = |Delta|
           and  x1:A1...x(j-1):A(j-1) |- V = mj{xj:Aj} .. mn{xn:An} type : kind
           and  x1:A1...x(j-1):A(j-1) |- w : +x1:A1... +x(j-1):A(j-1)
           and  Psi, G0 |- w1 : Psi+, G0[w1^-1]
           and  Psi |- w2 : Psi+-
           and  Psi+- |- t : Psi+, -x1:{{G0}} A1... -xj:{{G0}} Aj
           and  Psi+, -x1:{{G0}} A1...-x(j-1):{{G0}} A(j-1) |- z1: Psi+
           and  Psi+, -x1:{{G0}} A1...-x(j-1):{{G0}} A(j-1), G0 |- z2: x1:A1...x(j-1):A(j-1)
           then x1:A1...xn:An |- w' : +x1:A1... +xn:An
           and  Psi+- |- s' : +x1:A1 .. +xn:An
           and  Psi+- |- t' : Psi+, -x1:{{G0}} A1... -xn:{{G0}} An
           and  d' = |Delta'|
        *)
  (* head Ts (w, t, (d, Dplus, Dminus)) = (d', w', t', P')

             Invariant:
             If   a not in Ts  then d'= d+1,  P' makes a lemma call
             If   Ts = [a]     then d'= d     P' used directly the ih.
             If   Ts = a1 .. ai ... and ai = a
             then d' = d+i   and P' select ih, and then decomposes is, using
                  (i-1) Rights and 1 Left
          *)
  (* transformConc ((a, S), w) = P

       Invariant:
       If   Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w : PsiAll
       then P is proof term consisting of all - objects of S,
            defined in PsiAll
    *)
  (* traverse (Ts, c) = L'

       Invariant:
       If   Ts is a list of type families
       and  c is a type family which entries are currently traversed
       then L' is a list of cases
    *)
  (* traverseNeg (c'', Psi, (V, v), L) = ([w', d', PQ'], L')    [] means optional

           Invariant:
           If   Psi0 |- V : type
           and  Psi0 |- v : Psi
           and  V[v^-1] does not contain Skolem constants
           and  c'' is the name of the object constant currently considered
           and  L is a list of cases
           then L' list of cases and CL' extends CL
           and  Psi |- w' : Psi'   (Psi' is the context of all variables considered so far)
           and  d' is the length of Delta
           and  PQ'  is a pair, generating the proof term
        *)
  (*                                   (Names.decName (F.makectx Psi, Weaken.strengthenDec (D, v)))),
*)
  (* Clause head found *)
  (* traversePos (c, Psi, G, (V, v), [w', d', PQ'], L) =  ([w'', d'', PQ''], L'')

           Invariant:
           If   Psi, G |- V : type
           and  Psi, G |- v : Psi'       (s.t.  Psi' |- V[v^-1] : type exists)
           and V[v^-1] does not contain Skolem constants
           [ and Psi', G |- w' : Psi''
             and |Delta'| = d'    for a Delta'
             and PQ' can generate the proof term so far in Delta'; Psi''
           ]
           and  c is the name of the constant currently considered
           and  L is a list of cases
           then L'' list of cases and L'' extends L
           and  Psi |- w'' : Psi2
           and  |Delta''| = d''  for a Delta'
           and  PQ'' can genreate the proof term so far in Delta''; Psi2
        *)
  (* Lemma calls (no context block) *)
  (* provide typeCheckCtx from typecheck *)
  (* Lemma calls (under a context block) *)
  (* provide typeCheckCtx from typecheck *)
  (* change w1 to w1' and w2 to w2' below *)
  (* convertPro Ts = P'

       Invariant:
       If   Ts is a list of type families
       then P' is a conjunction of all programs resulting from converting
            the relational encoding of the function expressed by each type
            family in Ts into functional form
    *)
  let convertFor = convertFor
  let convertPro = convertPro
  let traverse = traverse
end
(*! sharing FunNames.FunSyn = FunSyn' !*)
(* functor FunSyn *)
