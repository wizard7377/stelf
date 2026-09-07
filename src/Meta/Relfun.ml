open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Subordinate
open! Subordinate
open! Modes
open! Modes.Modes_
open! Typecheck
open! Typecheck.Typecheck_
open! Index
open! Index.Index_
open! Opsem
open! Opsem.Opsem_
open! Compile
open! Compile.Compile_
open! Heuristic
open! Heuristic.Heuristic_
open! Timing
open! Timing.Timing_
open! Solvers
open! Solvers.Solvers_
open! M2
open! M2.M2_

(* # 1 "src/meta/Relfun.sig.ml" *)
open! Basis
open Modetable
open Funweaken
open Funnames
open Funsyn

(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)
include RELFUN
(* Signature RELFUN *)

(* # 1 "src/meta/Relfun.fun.ml" *)
open! Weaken
open! Global
open! Basis

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module RelFun (RelFun__0 : sig
  (* Converter from relational representation to a functional
   representation of proof terms *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure FunSyn' : FUNSYN !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing ModeSyn.IntSyn = FunSyn'.IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = FunSyn'.IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = FunSyn'.IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = FunSyn'.IntSyn !*)
  module Weaken : WEAKEN.WEAKEN

  (*! sharing Weaken.IntSyn = FunSyn'.IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = FunSyn'.IntSyn !*)
  module FunWeaken : FUNWEAKEN.FUNWEAKEN

  (*! sharing FunWeaken.FunSyn = FunSyn' !*)
  module FunNames : FUNNAMES.FUNNAMES
end) : RELFUN.RELFUN = struct
  (*! structure FunSyn = FunSyn' !*)
  exception Error = Error

  open RelFun__0

  open! struct
    module F = FunSyn
    module I = IntSyn
    module M = Modes.Modesyn.ModeSyn

    let rec ctxSub (a, s) = match a with
      | I.Null -> (I.Null, s)
      | I.Decl (g_, d_) ->
          let g'_, s' = ctxSub (g_, s) in
          (I.Decl (g'_, I.decSub d_ s'), I.dot1 s)

    let convertOneFor cid =
      let v_ =
        begin match I.sgnLookup cid with
        | I.ConDec (name, _, _, _, v_, I.Kind) -> v_
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
            ( (fun f_ -> F.All (F.Prim (Weaken.strengthenDec d_ w1), f'_ f_)),
              f''_ )
        | I.Pi ((d_, _), v_), M.Mapp (M.Marg (minus_, _), mS), w1, w2, n ->
            let f'_, f''_ =
              convertFor' (v_, mS, I.comp w1 I.shift, I.dot1 w2, n + 1)
            in
            (f'_, F.Ex (I.decSub d_ w2, f''_))
        | I.Uni I.Type, mnil_, _, _, _ -> ((fun f_ -> f_), F.True)
        | _ -> raise (Error "type family must be +/- moded")
      in
      let shiftPlus mS =
        let rec shiftPlus' (mnil_, n) = match mnil_ with
          | mnil_ -> n
          | M.Mapp (M.Marg (plus_, _), mS') -> shiftPlus' (mS', n + 1)
          | M.Mapp (M.Marg (minus_, _), mS') -> shiftPlus' (mS', n)
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

    let rec occursInExpN (k, a) = match a with
      | I.Uni _ -> false
      | I.Pi (dp_, v_) -> occursInDecP (k, dp_) || occursInExpN (k + 1, v_)
      | I.Root (h_, s_) -> occursInHead (k, h_) || occursInSpine (k, s_)
      | I.Lam (d_, v_) -> occursInDec (k, d_) || occursInExpN (k + 1, v_)
      | I.FgnExp (csid_, csfe) ->
          I.FgnExpStd.fold csid_ csfe
            (function
              | u_, b_ -> b_ || occursInExpN (k, Whnf.normalize (u_, I.id)))
            false

    and occursInHead (k, a) = match a with
      | I.BVar k' -> k = k'
      | I.Const _ -> false
      | I.Def _ -> false
      | I.FgnConst _ -> false

    and occursInSpine = function
      | _, I.Nil -> false
      | k, I.App (u_, s_) -> occursInExpN (k, u_) || occursInSpine (k, s_)

    and occursInDec (k, I.Dec (_, v_)) = occursInExpN (k, v_)
    and occursInDecP (k, (d_, _)) = occursInDec (k, d_)
    and occursInExp (k, u_) = occursInExpN (k, Whnf.normalize (u_, I.id))

    let dot1inv w = Weaken.strengthenSub (I.comp I.shift w) I.shift
    let shiftinv w = Weaken.strengthenSub w I.shift
    let eqIdx = function I.Idx n, I.Idx k -> n = k | _ -> false

    let peel w =
      begin if eqIdx (I.bvarSub 1 w, I.Idx 1) then dot1inv w else shiftinv w
      end

    let rec peeln (n, w) = match n with 0 -> w | n -> peeln (n - 1, peel w)

    let rec domain = function
      | g_, I.Dot (I.Idx _, s) -> domain (g_, s) + 1
      | I.Null, I.Shift 0 -> 0
      | (I.Decl _ as g_), I.Shift 0 -> domain (g_, I.Dot (I.Idx 1, I.Shift 1))
      | I.Decl (g_, _), I.Shift n -> domain (g_, I.Shift (n - 1))

    let strengthen (psi, (a, s_), w, m) =
      let mS =
        begin match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS
        end
      in
      let rec args = function
        | I.Nil, M.Mnil -> []
        | I.App (u_, s'_), M.Mapp (M.Marg (m', _), mS) ->
            let l_ = args (s'_, mS) in
            if M.modeEqual m m' then u_ :: l_ else l_
      in
      let rec strengthenArgs (a, s) = match a with
        | [] -> []
        | u_ :: l_ -> Weaken.strengthenExp u_ s :: strengthenArgs (l_, s)
      in
      let rec occursInArgs (n, a) = match a with
        | [] -> false
        | u_ :: l_ -> occursInExp (n, u_) || occursInArgs (n, l_)
      in
      let rec occursInPsi (n, a) = match a with
        | ([], l_) -> occursInArgs (n, l_)
        | (F.Prim (I.Dec (_, v_)) :: psi1, l_) ->
            occursInExp (n, v_) || occursInPsi (n + 1, (psi1, l_))
        | (F.Block (F.CtxBlock (l, g_)) :: psi1, l_) ->
            occursInG (n, g_, function n' -> occursInPsi (n', (psi1, l_)))
      and occursInG (n, a, k) = match a with
        | I.Null -> k n
        | I.Decl (g_, I.Dec (_, v_)) ->
            occursInG
              (n, g_, function n' -> occursInExp (n', v_) || k (n' + 1))
      in
      let occursBlock (g_, (psi2, l_)) =
        let rec occursBlock (a, n) = match a with
          | I.Null -> false
          | I.Decl (g_, d_) ->
              occursInPsi (n, (psi2, l_)) || occursBlock (g_, n + 1)
        in
        occursBlock (g_, 1)
      in
      let rec inBlock = function
        | I.Null, (bw, w1) -> (bw, w1)
        | I.Decl (g_, d_), (bw, w1) ->
            begin if eqIdx (I.bvarSub 1 w1, I.Idx 1) then
              inBlock (g_, (true, dot1inv w1))
            else inBlock (g_, (bw, Weaken.strengthenSub w1 I.shift))
            end
      in
      let rec blockSub a2 b2 = match a2, b2 with
        | I.Null, w -> (I.Null, w)
        | I.Decl (g_, I.Dec (name, v_)), w ->
            let g'_, w' = blockSub g_ w in
            let v'_ = Weaken.strengthenExp v_ w' in
            (I.Decl (g'_, I.Dec (name, v'_)), I.dot1 w')
      in
      let rec strengthen' (a, psi2, l_, w1) = match a with
        | I.Null -> (I.Null, I.id)
        | I.Decl (psi1, (F.Prim (I.Dec (name, v_)) as ld)) ->
            let bw, w1' =
              begin if eqIdx (I.bvarSub 1 w1, I.Idx 1) then (true, dot1inv w1)
              else (false, Weaken.strengthenSub w1 I.shift)
              end
            in
            begin if bw || occursInPsi (1, (psi2, l_)) then
              let psi1', w' = strengthen' (psi1, ld :: psi2, l_, w1') in
              let v'_ = Weaken.strengthenExp v_ w' in
              (I.Decl (psi1', F.Prim (I.Dec (name, v'_))), I.dot1 w')
            else
              let w2 = I.shift in
              let psi2', w2' = FunWeaken.strengthenPsi' psi2 w2 in
              let l'_ = strengthenArgs (l_, w2') in
              let psi1'', w' = strengthen' (psi1, psi2', l'_, w1') in
              (psi1'', I.comp w' I.shift)
            end
        | I.Decl (psi1, (F.Block (F.CtxBlock (name, g_)) as ld))
          ->
            let bw, w1' = inBlock (g_, (false, w1)) in
            begin if bw || occursBlock (g_, (psi2, l_)) then
              let psi1', w' = strengthen' (psi1, ld :: psi2, l_, w1') in
              let g''_, w'' = blockSub g_ w' in
              (I.Decl (psi1', F.Block (F.CtxBlock (name, g''_))), w'')
            else
              let w2 = I.Shift (I.ctxLength g_) in
              let psi2', w2' = FunWeaken.strengthenPsi' psi2 w2 in
              let l'_ = strengthenArgs (l_, w2') in
              strengthen' (psi1, psi2', l'_, w1')
            end
      in
      strengthen' (psi, [], args (s_, mS), w)

    let recursion l_ =
      let f_ = convertFor l_ in
      let rec name = function
        | a :: [] -> I.conDecName (I.sgnLookup a)
        | a :: l_ -> (I.conDecName (I.sgnLookup a) ^ "/") ^ name l_
      in
      function p -> F.Rec (F.MDec (Some (name l_), f_), p)

    let abstract a =
      let mS =
        begin match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS
        end
      in
      let v_ =
        begin match I.sgnLookup a with
        | I.ConDec (name, _, _, _, v_, I.Kind) -> v_
        | _ -> raise (Error "Type Constant declaration expected")
        end
      in
      let rec abstract' (a, w) = match a with
        | (_, mnil_) -> fun p -> p
        | (I.Pi ((d_, _), v2_), M.Mapp (M.Marg (plus_, _), mS)) ->
            let d'_ = Weaken.strengthenDec d_ w in
            let p_ = abstract' ((v2_, mS), I.dot1 w) in
            fun p -> F.Lam (F.Prim d'_, p_ p)
        | (I.Pi (_, v2_), M.Mapp (M.Marg (minus_, _), mS)) ->
            abstract' ((v2_, mS), I.comp w I.shift)
      in
      abstract' ((v_, mS), I.id)

    let transformInit (psi, (a, s_), w1) =
      let mS =
        begin match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS
        end
      in
      let v_ =
        begin match I.sgnLookup a with
        | I.ConDec (name, _, _, _, v_, I.Kind) -> v_
        | _ -> raise (Error "Type Constant declaration expected")
        end
      in
      let rec transformInit' = function
        | (nil_, mnil_), I.Uni I.Type, (w, s) -> (w, s)
        | ( (I.App (u_, s_), M.Mapp (M.Marg (minus_, _), mS)),
            I.Pi (_, v2_),
            (w, s) ) ->
            let w' = I.comp w I.shift in
            let s' = s in
            transformInit' ((s_, mS), v2_, (w', s'))
        | ( (I.App (u_, s_), M.Mapp (M.Marg (plus_, _), mS)),
            I.Pi ((I.Dec (name, v1_), _), v2_),
            (w, s) ) ->
            let v1' = Weaken.strengthenExp v1_ w in
            let w' = I.dot1 w in
            let u'_ = Weaken.strengthenExp u_ w1 in
            let s' = Whnf.dotEta (I.Exp u'_) s in
            transformInit' ((s_, mS), v2_, (w', s'))
      in
      transformInit' ((s_, mS), v_, (I.id, I.Shift (F.lfctxLength psi)))

    let transformDec (ts_, (psi, g0_), d, (a, s_), w1, w2, t0) =
      let mS =
        begin match ModeTable.modeLookup a with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS
        end
      in
      let v_ =
        begin match I.sgnLookup a with
        | I.ConDec (name, _, _, _, v_, I.Kind) -> v_
        | _ -> raise (Error "Type Constant declaration expected")
        end
      in
      let raiseExp (g_, u_, a) =
        let rec raiseExp' = function
          | I.Null -> (I.id, function x -> x)
          | I.Decl (g_, (I.Dec (_, v_) as d_)) ->
              let w, k = raiseExp' g_ in
              begin if
                Subordinate.Subordinate_.Subordinate.belowEq (I.targetFam v_) a
              then
                ( I.dot1 w,
                  function x -> k (I.Lam (Weaken.strengthenDec d_ w, x)) )
              else (I.comp w I.shift, k)
              end
        in
        let w, k = raiseExp' g_ in
        k (Weaken.strengthenExp u_ w)
      in
      let raiseType (g_, u_, a) =
        let rec raiseType' (b, n) = match b with
          | I.Null -> (I.id, (function x -> x), function s_ -> s_)
          | I.Decl (g_, (I.Dec (_, v_) as d_)) ->
              let w, k, k' = raiseType' (g_, n + 1) in
              begin if
                Subordinate.Subordinate_.Subordinate.belowEq (I.targetFam v_) a
              then
                ( I.dot1 w,
                  (function
                  | x -> k (I.Pi ((Weaken.strengthenDec d_ w, I.Maybe), x))),
                  function s_ -> I.App (I.Root (I.BVar n, I.Nil), s_) )
              else (I.comp w I.shift, k, k')
              end
        in
        let w, k, k' = raiseType' (g_, 2) in
        (k (Weaken.strengthenExp u_ w), I.Root (I.BVar 1, k' I.Nil))
      in
      let exchangeSub g0_ =
        let g0 = I.ctxLength g0_ in
        let rec exchangeSub' (k, s) = match k with
          | 0 -> s
          | k -> exchangeSub' (k - 1, I.Dot (I.Idx k, s))
        in
        I.Dot (I.Idx (g0 + 1), exchangeSub' (g0, I.Shift (g0 + 1)))
      in
      let rec transformDec' (d, a, b, c, e) = match a, b, c, e with
        | (nil_, mnil_), I.Uni I.Type, (z1, z2), (w, t) ->
            (w, t, (d, (fun (k, ds_) -> ds_ k), fun _ -> F.Empty))
        | (I.App (u_, s_), M.Mapp (M.Marg (minus_, _), mS)), I.Pi ((I.Dec (_, v1_), dp_), v2_), (z1, z2), (w, t) ->
            let g = I.ctxLength g0_ in
            let w1' = peeln (g, w1) in
            let g1_, _ = Weaken.strengthenCtx g0_ w1' in
            let g2_, _ = ctxSub (g1_, z1) in
            let v1'', ur = raiseType (g2_, I.EClo (v1_, z2), I.targetFam v1_) in
            let w' =
              begin match dp_ with
              | maybe_ -> I.dot1 w
              | no_ -> I.comp w I.shift
              end
            in
            let u0 = raiseExp (g0_, u_, I.targetFam v1'') in
            let u'_ = Weaken.strengthenExp u0 w2 in
            let t' = Whnf.dotEta (I.Exp u'_) t in
            let z1' = I.comp z1 I.shift in
            let xc = exchangeSub g0_ in
            let z2n = I.comp z2 (I.comp I.shift xc) in
            let ur' = I.EClo (ur, xc) in
            let z2' = Whnf.dotEta (I.Exp ur') z2n in
            let w'', t'', (d', dplus, dminus) =
              transformDec' (d + 1, (s_, mS), v2_, (z1', z2'), (w', t'))
            in
            (w'', t'', (d', dplus, function k -> F.Split (k, dminus 1)))
        | (I.App (u_, s_), M.Mapp (M.Marg (plus_, _), mS)), I.Pi ((I.Dec (name, v1_), _), v2_), (z1, z2), (w, t) ->
            let v1' = Weaken.strengthenExp v1_ w in
            let w' = I.dot1 w in
            let u'_ = Weaken.strengthenExp u_ w1 in
            let t' = t in
            let z1' = F.dot1n g0_ z1 in
            let z2' = I.Dot (I.Exp (I.EClo (u'_, z1')), z2) in
            let w'', t'', (d', dplus, dminus) =
              transformDec' (d + 1, (s_, mS), v2_, (z1, z2'), (w', t'))
            in
            ( w'',
              t'',
              (d', (fun (k, ds_) -> F.App ((k, u'_), dplus (1, ds_))), dminus)
            )
      in
      let w'', t'', (d', dplus, dminus) =
        transformDec'
          ( d,
            (s_, mS),
            v_,
            (I.id, I.Shift (domain (psi, t0) + I.ctxLength g0_)),
            (I.id, t0) )
      in
      let varHead ts_ (w'', t'', (d', dplus, dminus)) =
        let rec head' (b, d1, k1) = match b with
          | a' :: [] -> (d1, k1)
          | a' :: ts' ->
              begin if a = a' then (d1 + 1, function xx -> F.Left (xx, k1 1))
              else
                let d2, k2 = head' (ts', d1 + 1, k1) in
                (d2, function xx -> F.Right (xx, k2 1))
              end
        in
        let d2, k2 = head' (ts_, d', function xx -> dplus (xx, dminus)) in
        (d2, w'', t'', k2 d)
      in
      let lemmaHead (w'', t'', (d', dplus, dminus)) =
        let name = I.conDecName (I.sgnLookup a) in
        let l =
          begin match FunNames.nameLookup name with
          | None -> raise (Error (("Lemma " ^ name) ^ " not defined"))
          | Some lemma -> lemma
          end
        in
        (d' + 1, w'', t'', F.Lemma (l, dplus (1, dminus)))
      in
      begin if List.exists (function x -> x = a) ts_ then
        varHead ts_ (w'', t'', (d', dplus, dminus))
      else lemmaHead (w'', t'', (d', dplus, dminus))
      end

    let transformConc ((a, s_), w) =
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
            F.Inx (Weaken.strengthenExp u_ w, transformConc' (s'_, mS'))
      in
      transformConc' (s_, mS)

    let traverse (ts_, c) =
      let rec traverseNeg (c'', psi, a, l_) = match a with
        | (I.Pi (((I.Dec (_, v1_) as d_), maybe_), v2_), v) ->
            begin match
              traverseNeg
                ( c'',
                  I.Decl (psi, F.Prim (Weaken.strengthenDec d_ v)),
                  (v2_, I.dot1 v),
                  l_ )
            with
            | Some (w', d', pq'), l'_ -> (Some (peel w', d', pq'), l'_)
            | None, l'_ -> (None, l'_)
            end
        | (I.Pi (((I.Dec (_, v1_) as d_), no_), v2_), v) ->
            begin match
              traverseNeg (c'', psi, (v2_, I.comp v I.shift), l_)
            with
            | Some (w', d', pq'), l'_ ->
                traversePos
                  ( c'',
                    psi,
                    I.Null,
                    (Weaken.strengthenExp v1_ v, I.id),
                    Some (w', d', pq'),
                    l'_ )
            | None, l'_ ->
                traversePos
                  ( c'',
                    psi,
                    I.Null,
                    (Weaken.strengthenExp v1_ v, I.id),
                    None,
                    l'_ )
            end
        | ((I.Root (I.Const c', s_) as v_), v) ->
            begin if c = c' then
              let s'_ = Weaken.strengthenSpine s_ v in
              let psi', w' =
                strengthen (psi, (c', s'_), I.Shift (F.lfctxLength psi), M.Plus)
              in
              let w'', s'' = transformInit (psi', (c', s'_), w') in
              ( Some
                  ( w',
                    1,
                    ( (fun p -> (psi', s'', p)),
                      fun wf -> transformConc ((c', s'_), wf) ) ),
                l_ )
            else (None, l_)
            end
      and traversePos (c'', psi, g_, a, b, l_) = match g_, a, b with
        | g_, (I.Pi (((I.Dec (_, v1_) as d_), maybe_), v2_), v), Some (w, d, pq) ->
            begin match
              traversePos
                ( c'',
                  psi,
                  I.Decl (g_, Weaken.strengthenDec d_ v),
                  (v2_, I.dot1 v),
                  Some (I.dot1 w, d, pq),
                  l_ )
            with
            | Some (w', d', pq'), l'_ -> (Some (w', d', pq'), l'_)
            end
        | g_, (I.Pi (((I.Dec (_, v1_) as d_), no_), v2_), v), Some (w, d, pq) ->
            begin match
              traversePos
                (c'', psi, g_, (v2_, I.comp v I.shift), Some (w, d, pq), l_)
            with
            | Some (w', d', pq'), l'_ ->
                begin match
                  traverseNeg
                    ( c'',
                      I.Decl (psi, F.Block (F.CtxBlock (None, g_))),
                      (v1_, v),
                      l'_ )
                with
                | Some (w'', d'', (p'', q''_)), l'' ->
                    (Some (w', d', pq'), p'' (q''_ w'') :: l'')
                | None, l'' -> (Some (w', d', pq'), l'')
                end
            end
        | I.Null, (v_, v), Some (w1, d, (p_, q_)) ->
            let (I.Root (I.Const a', s_)) =
              Whnf.normalize (Weaken.strengthenExp v_ v, I.id)
            in
            let psi', w2 = strengthen (psi, (a', s_), w1, M.Minus) in
            ignore begin if !Global.doubleCheck then
                TypeCheck.typeCheck
                  (F.makectx psi') (I.Uni I.Type, I.Uni I.Kind)
              else ()
              end;
            let w3 = Weaken.strengthenSub w1 w2 in
            let d4, w4, t4, ds_ =
              transformDec (ts_, (psi', I.Null), d, (a', s_), w1, w2, w3)
            in
            ( Some
                ( w2,
                  d4,
                  ( (fun p ->
                      p_ (F.Let (ds_, F.Case (F.Opts [ (psi', t4, p) ])))),
                    q_ ) ),
              l_ )
        | g_, (v_, v), Some (w1, d, (p_, q_)) ->
            let (I.Root (I.Const a', s_)) = Weaken.strengthenExp v_ v in
            let (I.Decl (psi', F.Block (F.CtxBlock (name, g2_))) as dummy), w2 =
              strengthen
                ( I.Decl (psi, F.Block (F.CtxBlock (None, g_))),
                  (a', s_),
                  w1,
                  M.Minus )
            in
            ignore begin if !Global.doubleCheck then
                TypeCheck.typeCheck
                  (F.makectx dummy) (I.Uni I.Type, I.Uni I.Kind)
              else ()
              end;
            let g = I.ctxLength g_ in
            let w1' = peeln (g, w1) in
            let w2' = peeln (g, w2) in
            let g1_, _ = Weaken.strengthenCtx g_ w1' in
            let w3 = Weaken.strengthenSub w1' w2' in
            let d4, w4, t4, ds_ =
              transformDec (ts_, (psi', g_), d, (a', s_), w1, w2', w3)
            in
            ( Some
                ( w2',
                  d4,
                  ( (fun p ->
                      p_
                        (F.Let
                           ( F.New (F.CtxBlock (None, g1_), ds_),
                             F.Case (F.Opts [ (psi', t4, p) ]) ))),
                    q_ ) ),
              l_ )
        | g_, (I.Pi (((I.Dec (_, v1_) as d_), maybe_), v2_), v), None ->
            traversePos
              ( c'',
                psi,
                I.Decl (g_, Weaken.strengthenDec d_ v),
                (v2_, I.dot1 v),
                None,
                l_ )
        | g_, (I.Pi (((I.Dec (_, v1_) as d_), no_), v2_), v), None
          ->
            begin match
              traversePos (c'', psi, g_, (v2_, I.comp v I.shift), None, l_)
            with
            | None, l'_ ->
                begin match
                  traverseNeg
                    ( c'',
                      I.Decl (psi, F.Block (F.CtxBlock (None, g_))),
                      (v1_, v),
                      l'_ )
                with
                | Some (w'', d'', (p'', q''_)), l'' ->
                    (None, p'' (q''_ w'') :: l'')
                | None, l'' -> (None, l'')
                end
            end
        | g_, (v_, v), None -> (None, l_)
      in
      let rec traverseSig' (c'', l_) =
        begin if c'' = (fun (r, _) -> r) (I.sgnSize ()) then l_
        else
          begin match I.sgnLookup c'' with
          | I.ConDec (name, _, _, _, v_, I.Type) ->
              begin match traverseNeg (c'', I.Null, (v_, I.id), l_) with
              | Some (wf, d', (p'_, q'_)), l'_ ->
                  traverseSig' (c'' + 1, p'_ (q'_ wf) :: l'_)
              | None, l'_ -> traverseSig' (c'' + 1, l'_)
              end
          | _ -> traverseSig' (c'' + 1, l_)
          end
        end
      in
      traverseSig' (0, [])

    let convertPro ts_ =
      let convertOnePro a =
        let v_ =
          begin match I.sgnLookup a with
          | I.ConDec (name, _, _, _, v_, I.Kind) -> v_
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
        | a :: ts' -> F.Pair (convertOnePro a, convertPro' ts')
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

(* # 1 "src/meta/Relfun.sml.ml" *)
