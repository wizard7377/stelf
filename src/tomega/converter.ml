(* # 1 "src/tomega/converter.sig.ml" *)
open! Basis
module Tomega = Lambda_.Tomega

(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)
module type CONVERTER = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Error of string
  exception Error' of Tomega.sub_

  val convertFor : IntSyn.cid list -> Tomega.for_
  val convertPrg : IntSyn.cid list -> Tomega.prg_

  val installPrg :
    IntSyn.cid list ->
    IntSyn.cid * Tomega.lemma list * Tomega.lemma list (* projections *)

  (* selections *)
  val convertGoal : Tomega.dec_ IntSyn.ctx_ * IntSyn.exp_ -> Tomega.prg_
end
(* Signature CONVERTER *)

(* # 1 "src/tomega/converter.fun.ml" *)
open! Redundant
open! Basis
open Worldcheck_

module Converter (Converter__0 : sig
  (* Converter from relational representation to a functional
   representation of proof terms *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing ModeSyn.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module TomegaPrint : Tomegaprint.TOMEGAPRINT

  (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
  (*! sharing TomegaPrint.Tomega = Tomega' !*)
  module WorldSyn : Worldcheck_.WORLDSYN

  (*! sharing WorldSyn.IntSyn = IntSyn' !*)
  (*! sharing WorldSyn.Tomega = Tomega' !*)
  module Worldify : WORLDIFY

  (*! sharing Worldify.IntSyn = IntSyn' !*)
  (*! sharing Worldify.Tomega = Tomega' !*)
  module TomegaTypeCheck : Tomega_typecheck.TOMEGATYPECHECK

  (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
  (*! sharing TomegaTypeCheck.Tomega = Tomega' !*)
  module Subordinate : SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module TypeCheck : Typecheck_.TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Redundant : REDUNDANT
  module TomegaAbstract : Tomega_abstract.TOMEGAABSTRACT
end) : CONVERTER = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  exception Error of string
  exception Error' of Tomega.sub_

  open! struct
    module T = Tomega
    module I = IntSyn
    module M = ModeSyn
    module S = Subordinate
    module A = Abstract
    module TomegaTypeCheck = Converter__0.TomegaTypeCheck
    module TA = Converter__0.TomegaAbstract

    let rec isIdx1 = function I.Idx 1 -> true | _ -> false

    let rec modeSpine a =
      begin match ModeTable.modeLookup a with
      | None -> raise (Error "Mode declaration expected")
      | Some mS -> mS
      end

    let rec typeOf a =
      begin match I.sgnLookup a with
      | I.ConDec (name, _, _, _, v_, kind_) -> v_
      | _ -> raise (Error "Type Constant declaration expected")
      end

    let rec nameOf a =
      begin match I.sgnLookup a with
      | I.ConDec (name, _, _, _, v_, kind_) -> name
      | _ -> raise (Error "Type Constant declaration expected")
      end

    let rec chatter chlev f =
      begin if !Global.chatter >= chlev then print ("[tomega] " ^ f ()) else ()
      end

    let rec strengthenExp (u_, s) = Whnf.normalize (Whnf.cloInv (u_, s), I.id)
    let rec strengthenSub (s, t) = Whnf.compInv (s, t)

    let rec strengthenDec = function
      | I.Dec (name, v_), s -> I.Dec (name, strengthenExp (v_, s))
      | I.BDec (name, (l_, t)), s -> I.BDec (name, (l_, strengthenSub (t, s)))

    let rec strengthenCtx = function
      | null_, s -> (I.Null, s)
      | I.Decl (g_, d_), s ->
          let g'_, s' = strengthenCtx (g_, s) in
          (I.Decl (g'_, strengthenDec (d_, s')), I.dot1 s')

    let rec strengthenFor = function
      | True, s -> T.True
      | T.And (f1_, f2_), s ->
          T.And (strengthenFor (f1_, s), strengthenFor (f2_, s))
      | T.All ((T.UDec d_, q_), f_), s ->
          T.All
            ((T.UDec (strengthenDec (d_, s)), q_), strengthenFor (f_, I.dot1 s))
      | T.Ex ((d_, q_), f_), s ->
          T.Ex ((strengthenDec (d_, s), q_), strengthenFor (f_, I.dot1 s))

    let rec strengthenOrder = function
      | Order.Arg ((u_, s1), (v_, s2)), s ->
          Order.Arg ((u_, strengthenSub (s1, s)), (v_, strengthenSub (s2, s)))
      | Order.Simul os_, s ->
          Order.Simul (map (function o_ -> strengthenOrder (o_, s)) os_)
      | Order.Lex os_, s ->
          Order.Lex (map (function o_ -> strengthenOrder (o_, s)) os_)

    let rec strengthenTC = function
      | T.Base o_, s -> T.Base (strengthenOrder (o_, s))
      | T.Conj (tc1_, tc2_), s ->
          T.Conj (strengthenTC (tc1_, s), strengthenTC (tc2_, s))
      | T.Abs (d_, tc_), s ->
          T.Abs (strengthenDec (d_, s), strengthenTC (tc_, I.dot1 s))

    let rec strengthenSpine = function
      | nil_, t -> I.Nil
      | I.App (u_, s_), t ->
          I.App (strengthenExp (u_, t), strengthenSpine (s_, t))

    let rec strengthenPsi = function
      | null_, s -> (I.Null, s)
      | I.Decl (psi_, T.UDec d_), s ->
          let psi'_, s' = strengthenPsi (psi_, s) in
          (I.Decl (psi'_, T.UDec (strengthenDec (d_, s'))), I.dot1 s')
      | I.Decl (psi_, T.PDec (name, f_, None, None)), s ->
          let psi'_, s' = strengthenPsi (psi_, s) in
          ( I.Decl (psi'_, T.PDec (name, strengthenFor (f_, s'), None, None)),
            I.dot1 s' )

    let rec strengthenPsi' = function
      | [], s -> ([], s)
      | T.UDec d_ :: psi_, s ->
          let d'_ = strengthenDec (d_, s) in
          let s' = I.dot1 s in
          let psi''_, s'' = strengthenPsi' (psi_, s') in
          (T.UDec d'_ :: psi''_, s'')

    let rec ctxSub = function
      | null_, s -> (I.Null, s)
      | I.Decl (g_, d_), s ->
          let g'_, s' = ctxSub (g_, s) in
          (I.Decl (g'_, I.decSub (d_, s')), I.dot1 s)

    let rec validMode = function
      | M.Mnil -> ()
      | M.Mapp (M.Marg (M.Plus, _), mS) -> validMode mS
      | M.Mapp (M.Marg (M.Minus, _), mS) -> validMode mS
      | M.Mapp (M.Marg (M.Star, _), mS) ->
          raise (Error "+ or - mode expected, * found")

    let rec validSig = function
      | psi0_, [] -> ()
      | psi0_, (g_, v_) :: sig_ ->
          let rec append = function
            | g_, null_ -> g_
            | g_, I.Decl (g'_, d_) -> I.Decl (append (g_, g'_), d_)
          in
          begin
            TypeCheck.typeCheck
              (T.coerceCtx (append (psi0_, T.embedCtx g_)), (v_, I.Uni I.Type));
            validSig (psi0_, sig_)
          end

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
      let _ = validMode mS in
      let rec convertFor' = function
        | I.Pi ((d_, _), v_), M.Mapp (M.Marg (M.Plus, _), mS), w1, w2, n ->
            let f'_, f''_ =
              convertFor' (v_, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n - 1)
            in
            ( (function
              | f_ ->
                  T.All ((T.UDec (strengthenDec (d_, w1)), T.Explicit), f'_ f_)),
              f''_ )
        | I.Pi ((d_, _), v_), M.Mapp (M.Marg (M.Minus, _), mS), w1, w2, n ->
            let f'_, f''_ =
              convertFor' (v_, mS, I.comp (w1, I.shift), I.dot1 w2, n + 1)
            in
            (f'_, T.Ex ((I.decSub (d_, w2), T.Explicit), f''_))
        | I.Uni type_, M.Mnil, _, _, _ -> ((function f_ -> f_), T.True)
        | _ -> raise (Error "type family must be +/- moded")
      in
      let rec shiftPlus mS =
        let rec shiftPlus' = function
          | M.Mnil, n -> n
          | M.Mapp (M.Marg (M.Plus, _), mS'), n -> shiftPlus' (mS', n + 1)
          | M.Mapp (M.Marg (M.Minus, _), mS'), n -> shiftPlus' (mS', n)
        in
        shiftPlus' (mS, 0)
      in
      let n = shiftPlus mS in
      let f_, f'_ = convertFor' (v_, mS, I.id, I.Shift n, n) in
      f_ f'_

    let rec createIH = function
      | [] -> raise (Error "Empty theorem")
      | a :: [] ->
          let name = I.conDecName (I.sgnLookup a) in
          let f_ = convertOneFor a in
          (name, f_)
      | a :: l_ ->
          let name = I.conDecName (I.sgnLookup a) in
          let f_ = convertOneFor a in
          let name', f'_ = createIH l_ in
          ((name ^ "/") ^ name', T.And (f_, f'_))

    let rec convertFor l_ =
      let _, f'_ = createIH l_ in
      f'_

    let rec occursInExpN = function
      | k, I.Uni _ -> false
      | k, I.Pi (dp_, v_) -> occursInDecP (k, dp_) || occursInExpN (k + 1, v_)
      | k, I.Root (h_, s_) -> occursInHead (k, h_) || occursInSpine (k, s_)
      | k, I.Lam (d_, v_) -> occursInDec (k, d_) || occursInExpN (k + 1, v_)
      | k, I.FgnExp (csid_, csfe) ->
          I.FgnExpStd.fold (csid_, csfe)
            (function
              | u_, dp_ -> dp_ || occursInExp (k, Whnf.normalize (u_, I.id)))
            false

    and occursInHead = function
      | k, I.BVar k' -> k = k'
      | k, I.Const _ -> false
      | k, I.Def _ -> false
      | k, I.FgnConst _ -> false
      | k, I.Proj _ -> false

    and occursInSpine = function
      | _, nil_ -> false
      | k, I.App (u_, s_) -> occursInExpN (k, u_) || occursInSpine (k, s_)

    and occursInDec (k, I.Dec (_, v_)) = occursInExpN (k, v_)
    and occursInDecP (k, (d_, _)) = occursInDec (k, d_)
    and occursInExp (k, u_) = occursInExpN (k, Whnf.normalize (u_, I.id))

    let rec dot1inv w = strengthenSub (I.comp (I.shift, w), I.shift)
    let rec shiftinv w = strengthenSub (w, I.shift)

    let rec peel w =
      begin if isIdx1 (I.bvarSub (1, w)) then dot1inv w else shiftinv w
      end

    let rec peeln = function 0, w -> w | n, w -> peeln (n - 1, peel w)

    let rec popn = function
      | 0, psi_ -> (psi_, I.Null)
      | n, I.Decl (psi_, T.UDec d_) ->
          let psi'_, g'_ = popn (n - 1, psi_) in
          (psi'_, I.Decl (g'_, d_))

    let rec domain = function
      | g_, I.Dot (I.Idx _, s) -> domain (g_, s) + 1
      | null_, I.Shift 0 -> 0
      | (I.Decl _ as g_), I.Shift 0 -> domain (g_, I.Dot (I.Idx 1, I.Shift 1))
      | I.Decl (g_, _), I.Shift n -> domain (g_, I.Shift (n - 1))

    let rec strengthen (psi_, (a, s_), w, m) =
      let mS = modeSpine a in
      let rec args = function
        | nil_, M.Mnil -> []
        | I.App (u_, s'_), M.Mapp (M.Marg (m', _), mS) ->
            let l_ = args (s'_, mS) in
            begin match M.modeEqual (m, m') with
            | true -> u_ :: l_
            | false -> l_
            end
      in
      let rec strengthenArgs = function
        | [], s -> []
        | u_ :: l_, s -> strengthenExp (u_, s) :: strengthenArgs (l_, s)
      in
      let rec occursInArgs = function
        | n, [] -> false
        | n, u_ :: l_ -> occursInExp (n, u_) || occursInArgs (n, l_)
      in
      let rec occursInPsi = function
        | n, ([], l_) -> occursInArgs (n, l_)
        | n, (T.UDec (I.Dec (_, v_)) :: psi1_, l_) ->
            occursInExp (n, v_) || occursInPsi (n + 1, (psi1_, l_))
        | n, (T.UDec (I.BDec (_, (cid, s))) :: psi1_, l_) ->
            let (I.BlockDec (_, _, g_, _)) = I.sgnLookup cid in
            occursInSub (n, s, g_) || occursInPsi (n + 1, (psi1_, l_))
      and occursInSub = function
        | _, _, null_ -> false
        | n, I.Shift k, g_ ->
            occursInSub (n, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), g_)
        | n, I.Dot (I.Idx k, s), I.Decl (g_, _) ->
            n = k || occursInSub (n, s, g_)
        | n, I.Dot (I.Exp u_, s), I.Decl (g_, _) ->
            occursInExp (n, u_) || occursInSub (n, s, g_)
        | n, I.Dot (I.Block _, s), I.Decl (g_, _) -> occursInSub (n, s, g_)
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
            if isIdx1 (I.bvarSub (1, w1)) then inBlock (g_, (true, dot1inv w1))
            else inBlock (g_, (bw, strengthenSub (w1, I.shift)))
          end
      in
      let rec blockSub = function
        | null_, w -> (I.Null, w)
        | I.Decl (g_, I.Dec (name, v_)), w ->
            let g'_, w' = blockSub (g_, w) in
            let v'_ = strengthenExp (v_, w') in
            (I.Decl (g'_, I.Dec (name, v'_)), I.dot1 w')
      in
      let rec strengthen' = function
        | null_, psi2_, l_, w1 -> (I.Null, I.id, I.id)
        | I.Decl (psi1_, (T.UDec (I.Dec (name, v_)) as ld_)), psi2_, l_, w1 ->
          begin
            if isIdx1 (I.bvarSub (1, w1)) then
              let w1' = dot1inv w1 in
              let psi1'_, w', z' = strengthen' (psi1_, ld_ :: psi2_, l_, w1') in
              let v'_ = strengthenExp (v_, w') in
              (I.Decl (psi1'_, T.UDec (I.Dec (name, v'_))), I.dot1 w', I.dot1 z')
            else begin
              if occursInPsi (1, (psi2_, l_)) then
                let w1' = strengthenSub (w1, I.shift) in
                let psi1'_, w', z' =
                  strengthen' (psi1_, ld_ :: psi2_, l_, w1')
                in
                let v'_ = strengthenExp (v_, w') in
                ( I.Decl (psi1'_, T.UDec (I.Dec (name, v'_))),
                  I.dot1 w',
                  I.comp (z', I.shift) )
              else
                let w1' = strengthenSub (w1, I.shift) in
                let w2 = I.shift in
                let psi2'_, w2' = strengthenPsi' (psi2_, w2) in
                let l'_ = strengthenArgs (l_, w2') in
                let psi1''_, w', z' = strengthen' (psi1_, psi2'_, l'_, w1') in
                (psi1''_, I.comp (w', I.shift), z')
            end
          end
        | I.Decl (psi1_, (T.PDec (name, f_, None, None) as d_)), psi2_, l_, w1
          ->
            let w1' = dot1inv w1 in
            let psi1'_, w', z' = strengthen' (psi1_, d_ :: psi2_, l_, w1') in
            let f'_ = strengthenFor (f_, w') in
            ( I.Decl (psi1'_, T.PDec (name, f'_, None, None)),
              I.dot1 w',
              I.dot1 z' )
        | ( I.Decl (psi1_, (T.UDec (I.BDec (name, (cid, s))) as ld_)),
            psi2_,
            l_,
            w1 ) ->
            let w1' = dot1inv w1 in
            let psi1'_, w', z' = strengthen' (psi1_, ld_ :: psi2_, l_, w1') in
            let s' = strengthenSub (s, w') in
            ( I.Decl (psi1'_, T.UDec (I.BDec (name, (cid, s')))),
              I.dot1 w',
              I.dot1 z' )
      in
      strengthen' (psi_, [], args (s_, mS), w)

    let rec lookupIH (psi_, l_, a) =
      let rec lookupIH' (b :: l_, a, k) =
        begin if a = b then k else lookupIH' (l_, a, k - 1)
        end
      in
      lookupIH' (l_, a, I.ctxLength psi_)

    let rec createIHSub (psi_, l_) = T.Shift (I.ctxLength psi_ - 1)

    let rec transformInit (psi_, l_, (a, s_), w1) =
      let mS = modeSpine a in
      let v_ = typeOf a in
      let rec transformInit' = function
        | (nil_, M.Mnil), I.Uni type_, (w, s) -> (w, s)
        | ( (I.App (u_, s_), M.Mapp (M.Marg (M.Minus, _), mS)),
            I.Pi (_, v2_),
            (w, s) ) ->
            let w' = I.comp (w, I.shift) in
            let s' = s in
            transformInit' ((s_, mS), v2_, (w', s'))
        | ( (I.App (u_, s_), M.Mapp (M.Marg (M.Plus, _), mS)),
            I.Pi ((I.Dec (name, v1_), _), v2_),
            (w, s) ) ->
            let v1'_ = strengthenExp (v1_, w) in
            let w' = I.dot1 w in
            let u'_ = strengthenExp (u_, w1) in
            let s' = T.dotEta (T.Exp u'_, s) in
            transformInit' ((s_, mS), v2_, (w', s'))
      in
      transformInit' ((s_, mS), v_, (I.id, createIHSub (psi_, l_)))

    let rec transformConc ((a, s_), w) =
      let rec transformConc' = function
        | nil_, M.Mnil -> T.Unit
        | I.App (u_, s'_), M.Mapp (M.Marg (M.Plus, _), mS') ->
            transformConc' (s'_, mS')
        | I.App (u_, s'_), M.Mapp (M.Marg (M.Minus, _), mS') ->
            T.PairExp (strengthenExp (u_, w), transformConc' (s'_, mS'))
      in
      transformConc' (s_, modeSpine a)

    let rec renameExp arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | f, (I.Uni _ as u_) -> u_
      | f, I.Pi ((d_, dp_), v_) -> I.Pi ((renameDec f d_, dp_), renameExp f v_)
      | f, I.Root (h_, s_) -> I.Root (renameHead f h_, renameSpine f s_)
      | f, I.Lam (d_, u_) -> I.Lam (renameDec f d_, renameExp f u_)
      end

    and renameDec f (I.Dec (x, v_)) = I.Dec (x, renameExp f v_)

    and renameHead arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | f, I.Proj (bi, i) -> f (bi, i)
      | f, h_ -> h_
      end

    and renameSpine arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | f, nil_ -> I.Nil
      | f, I.App (u_, s_) -> I.App (renameExp f u_, renameSpine f s_)
      end

    let rec rename (I.BDec (_, (c, s)), v_) =
      let g_, l_ = I.constBlock c in
      let rec makeSubst = function
        | n, g_, s, [], f -> (g_, f)
        | n, g_, s, (I.Dec (x, v'_) as d_) :: l_, f -> begin
            if Subordinate.belowEq (I.targetFam v'_, I.targetFam v_) then
              makeSubst (n + 1, I.Decl (g_, I.decSub (d_, s)), I.dot1 s, l_, f)
            else makeSubst (n, g_, I.comp (s, I.shift), l_, f)
          end
      in
      let g'_, f = makeSubst (1, g_, s, l_, function x, i -> I.Proj (x, i)) in
      (g_, renameExp f v_)

    let rec append = function
      | g_, null_ -> g_
      | g_, I.Decl (g'_, d_) -> I.Decl (append (g_, g'_), d_)

    let rec traverseNeg arg__7 arg__8 =
      begin match (arg__7, arg__8) with
      | ( (l_, wmap, projs),
          ((psi0_, psi_), I.Pi (((I.Dec (_, v1_) as d_), maybe_), v2_), w) ) ->
        begin
          match
            traverseNeg (l_, wmap, projs)
              ((psi0_, I.Decl (psi_, T.UDec d_)), v2_, I.dot1 w)
          with
          | Some (w', pq'_) -> Some (peel w', pq'_)
        end
      | ( (l_, wmap, projs),
          ((psi0_, psi_), I.Pi (((I.Dec (_, v1_) as d_), no_), v2_), w) ) ->
        begin
          match
            traverseNeg (l_, wmap, projs)
              ((psi0_, I.Decl (psi_, T.UDec d_)), v2_, I.comp (w, I.shift))
          with
          | Some (w', pq'_) ->
              traversePos (l_, wmap, projs)
                ((psi0_, psi_, I.Null), v1_, Some (peel w', pq'_))
        end
      | (l_, wmap, projs), ((psi0_, psi_), I.Root (I.Const a, s_), w) ->
          let psi1_ = append (psi0_, psi_) in
          let w0 = I.Shift (I.ctxLength psi_) in
          let psi'_, w', _ = strengthen (psi1_, (a, s_), w0, M.Plus) in
          let w'', s'' = transformInit (psi'_, l_, (a, s_), w') in
          let _ = TomegaTypeCheck.checkCtx psi'_ in
          Some
            ( w',
              ((function p_ -> (psi'_, s'', p_)), transformConc ((a, s_), w)) )
      end

    and traversePos arg__9 arg__10 =
      begin match (arg__9, arg__10) with
      | ( (l_, wmap, projs),
          ( (psi0_, psi_, g_),
            I.Pi (((I.BDec (x, (c, s)) as d_), _), v_),
            Some (w1, (p_, q_)) ) ) ->
          let c' = wmap c in
          let n = I.ctxLength psi0_ + I.ctxLength g_ in
          let gsome_, lpi_ = I.constBlock c in
          let _ =
            TypeCheck.typeCheckCtx
              (T.coerceCtx (append (append (psi0_, psi_), T.embedCtx g_)))
          in
          let _ =
            TypeCheck.typeCheckSub
              ( T.coerceCtx (append (append (psi0_, psi_), T.embedCtx g_)),
                s,
                gsome_ )
          in
          let gsome'_, lpi'_ = I.constBlock c' in
          let _ =
            TypeCheck.typeCheckCtx
              (T.coerceCtx (append (append (psi0_, psi_), T.embedCtx g_)))
          in
          let _ =
            TypeCheck.typeCheckSub
              ( T.coerceCtx (append (append (psi0_, psi_), T.embedCtx g_)),
                s,
                gsome'_ )
          in
          traversePos (l_, wmap, projs)
            ( (psi0_, psi_, I.Decl (g_, I.BDec (x, (c', s)))),
              v_,
              Some (I.dot1 w1, (p_, q_)) )
      | ( (l_, wmap, projs),
          ((psi0_, g_, b_), (I.Root (I.Const a, s_) as v_), Some (w1, (p_, q_)))
        ) ->
          let psi1_ = append (psi0_, append (g_, T.embedCtx b_)) in
          let _ =
            TomegaTypeCheck.checkCtx
              (append (append (psi0_, g_), T.embedCtx b_))
          in
          let n = domain (psi1_, w1) in
          let m = I.ctxLength psi0_ in
          let rec lookupbase a =
            let s = I.conDecName (I.sgnLookup a) in
            let l = T.lemmaName s in
            let (T.ValDec (_, p_, f_)) = T.lemmaLookup l in
            (T.Const l, f_)
          in
          let rec lookup = function
            | (b :: [], None, f_), a -> begin
                if a = b then
                  let p_ = T.Var n in
                  (p_, f_)
                else lookupbase a
              end
            | (b :: [], Some (lemma :: []), f_), a -> begin
                if a = b then
                  let p_ = T.Redex (T.Const lemma, T.AppPrg (T.Var n, T.Nil)) in
                  (p_, f_)
                else lookupbase a
              end
            | (b :: l_, Some (lemma :: lemmas), T.And (f1_, f2_)), a -> begin
                if a = b then
                  let p_ = T.Redex (T.Const lemma, T.AppPrg (T.Var n, T.Nil)) in
                  (p_, f1_)
                else lookup ((l_, Some lemmas, f2_), a)
              end
          in
          let hp_, f_ =
            begin if I.ctxLength psi0_ > 0 then
              let (T.PDec (_, f0_, _, _)) = I.ctxLookup (psi0_, 1) in
              lookup ((l_, projs, f0_), a)
            else lookupbase a
            end
          in
          let rec apply ((s_, mS), ft_) = applyW ((s_, mS), T.whnfFor ft_)
          and applyW = function
            | (nil_, M.Mnil), ft'_ -> (T.Nil, T.forSub ft'_)
            | ( (I.App (u_, s_), M.Mapp (M.Marg (M.Plus, _), mS)),
                (T.All (d_, f'_), t') ) ->
                let u'_ = strengthenExp (u_, w1) in
                let s''_, f''_ =
                  apply ((s_, mS), (f'_, T.Dot (T.Exp u'_, t')))
                in
                (T.AppExp (u'_, s''_), f''_)
            | (I.App (u_, s_), M.Mapp (M.Marg (M.Minus, _), mS)), ft_ ->
                applyW ((s_, mS), ft_)
          in
          let s''_, f''_ = apply ((s_, modeSpine a), (f_, T.id)) in
          let _ =
            TomegaTypeCheck.checkFor
              ( append (append (psi0_, g_), T.embedCtx b_),
                T.forSub (f''_, T.embedSub w1) )
          in
          let p''_ = T.Redex (hp_, s''_) in
          let b = I.ctxLength b_ in
          let w1' = peeln (b, w1) in
          let b'_, _ = strengthenCtx (b_, w1') in
          let n' = n - I.ctxLength b'_ in
          let rec subCtx = function
            | null_, s -> (I.Null, s)
            | I.Decl (g_, d_), s ->
                let g'_, s' = subCtx (g_, s) in
                (I.Decl (g'_, I.decSub (d_, s')), I.dot1 s')
          in
          let b''_, _ = subCtx (b'_, w1') in
          let _ =
            TomegaTypeCheck.checkCtx
              (append (append (psi0_, g_), T.embedCtx b''_))
          in
          let gb'_, iota = T.deblockify b'_ in
          let _ =
            try TypeCheck.typeCheckSub (gb'_, T.coerceSub iota, b'_)
            with TypeCheck.Error _ -> raise (Error' iota)
          in
          let rr_ = T.forSub (f''_, iota) in
          let f'''_ = TA.raiseFor (gb'_, (rr_, I.id)) in
          let rec lift = function
            | null_, p_ -> p_
            | I.Decl (g_, d_), p_ ->
                let bint_, _ = T.deblockify (I.Decl (I.Null, d_)) in
                lift (g_, T.New (T.Lam (T.UDec d_, p_)))
          in
          let p'''_ = lift (b'_, p''_) in
          let _ = TomegaTypeCheck.checkCtx (append (psi0_, g_)) in
          let _ =
            TomegaTypeCheck.checkFor
              (append (psi0_, g_), T.forSub (f'''_, T.embedSub w1'))
          in
          let psi1''_, w2, z2 = strengthen (psi1_, (a, s_), w1, M.Minus) in
          let w3 = peeln (b, w2) in
          let z3 = peeln (b, z2) in
          let psi2_, b3'_ = popn (b, psi1''_) in
          let pat'_ = transformConc ((a, s_), w2) in
          let f4_ = T.forSub (f'''_, T.embedSub z3) in
          let _ = TomegaTypeCheck.checkCtx psi1''_ in
          let _ = TomegaTypeCheck.checkCtx (append (psi2_, T.embedCtx b3'_)) in
          let _ =
            try TomegaTypeCheck.checkFor (psi2_, f4_)
            with _ -> raise (Error "")
          in
          let b3_, sigma3 = T.deblockify b3'_ in
          let pat''_ = T.normalizePrg (pat'_, sigma3) in
          let pat_ = TA.raisePrg (b3_, pat''_, f4_) in
          let _ = TomegaTypeCheck.checkPrg (psi2_, (pat_, f4_)) in
          let t = T.Dot (T.Prg pat_, T.embedSub z3) in
          Some
            ( w3,
              ( (function
                | p ->
                    p_
                      (T.Let
                         ( T.PDec (None, f'''_, None, None),
                           p'''_,
                           T.Case (T.Cases [ (psi2_, t, p) ]) ))),
                q_ ) )
      end

    let rec traverse (psi0_, l_, sig_, wmap, projs) =
      let rec traverseSig' = function
        | [] -> []
        | (g_, v_) :: sig_ -> begin
            TypeCheck.typeCheck
              (append (T.coerceCtx psi0_, g_), (v_, I.Uni I.Type));
            begin match
              traverseNeg (l_, wmap, projs) ((psi0_, T.embedCtx g_), v_, I.id)
            with
            | Some (wf, (p'_, q'_)) -> traverseSig' sig_ @ [ p'_ q'_ ]
            end
          end
      in
      traverseSig' sig_

    let rec transformWorlds (fams, T.Worlds cids) =
      let rec transformList = function
        | [], w -> []
        | (I.Dec (x, v_) as d_) :: l_, w -> begin
            if
              List.foldr
                (function
                  | a, b -> b && Subordinate.belowEq (a, I.targetFam v_))
                true fams
            then transformList (l_, I.comp (w, I.shift))
            else
              let l'_ = transformList (l_, I.dot1 w) in
              I.Dec (x, strengthenExp (v_, w)) :: l'_
          end
      in
      let rec transformWorlds' = function
        | [] -> ([], function c -> raise (Error "World not found"))
        | cid :: cids' -> (
            let (I.BlockDec (s, m, g_, l_)) = I.sgnLookup cid in
            let l'_ = transformList (l_, I.id) in
            let cids'', wmap = transformWorlds' cids' in
            let cid' = I.sgnAdd (I.BlockDec (s, m, g_, l'_)) in
            ( cid' :: cids'',
              function c -> begin if c = cid then cid' else wmap c end ))
      in
      let cids', wmap = transformWorlds' cids in
      (T.Worlds cids', wmap)

    let rec dynamicSig (psi0_, a, T.Worlds cids) =
      let rec findDec = function
        | g_, _, [], w, sig_ -> sig_
        | g_, n, d_ :: l_, w, sig_ ->
            let (I.Dec (x, v'_) as d'_) = I.decSub (d_, w) in
            let b = I.targetFam v'_ in
            let sig'_ =
              begin if b = a then (g_, Whnf.normalize (v'_, I.id)) :: sig_
              else sig_
              end
            in
            findDec
              ( g_,
                n + 1,
                l_,
                I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, n), I.Nil)), w),
                sig'_ )
      in
      let rec mediateSub = function
        | null_ -> (I.Null, I.Shift (I.ctxLength psi0_))
        | I.Decl (g_, d_) ->
            let g0_, s' = mediateSub g_ in
            let d'_ = I.decSub (d_, s') in
            (I.Decl (g0_, d'_), I.dot1 s')
      in
      let rec findDecs' = function
        | [], sig_ -> sig_
        | cid :: cids', sig_ ->
            let (I.BlockDec (s, m, g_, l_)) = I.sgnLookup cid in
            let g0_, s' = mediateSub g_ in
            let d'_ = Names.decName (g0_, I.BDec (None, (cid, s'))) in
            let s'' = I.comp (s', I.shift) in
            let sig'_ = findDec (I.Decl (g0_, d'_), 1, l_, s'', sig_) in
            findDecs' (cids', sig'_)
      in
      findDecs' (cids, [])

    let rec staticSig = function
      | psi0_, [] -> []
      | psi0_, I.ConDec (name, _, _, _, v_, type_) :: sig_ ->
          (I.Null, Whnf.normalize (v_, I.Shift (I.ctxLength psi0_)))
          :: staticSig (psi0_, sig_)

    let rec name = function
      | a :: [] -> I.conDecName (I.sgnLookup a)
      | a :: l_ -> (I.conDecName (I.sgnLookup a) ^ "/") ^ name l_

    let rec convertPrg (l_, projs) =
      let name, f0_ = createIH l_ in
      let d0_ = T.PDec (Some name, f0_, None, None) in
      let psi0_ = I.Decl (I.Null, d0_) in
      let prec_ = function p -> T.Rec (d0_, p) in
      let rec convertWorlds = function
        | a :: [] ->
            let w_ = WorldSyn.lookup a in
            w_
        | a :: l'_ ->
            let w_ = WorldSyn.lookup a in
            let w'_ = convertWorlds l'_ in
            begin if T.eqWorlds (w_, w'_) then w'_
            else raise (Error "Type families different in different worlds")
            end
      in
      let w_ = convertWorlds l_ in
      let w'_, wmap = transformWorlds (l_, w_) in
      let rec convertOnePrg (a, f_) =
        let name = nameOf a in
        let v_ = typeOf a in
        let mS = modeSpine a in
        let sig_ = Worldify.worldify a in
        let dynSig = dynamicSig (psi0_, a, w_) in
        let statSig = staticSig (psi0_, sig_) in
        let _ =
          map
            (function
              | I.ConDec (_, _, _, _, u_, v_) -> TypeCheck.check (u_, I.Uni v_))
            sig_
        in
        let _ = validSig (psi0_, statSig) in
        let _ = validSig (psi0_, dynSig) in
        let c0_ = traverse (psi0_, l_, dynSig, wmap, projs) in
        let rec init = function
          | T.All ((d_, _), f'_) -> (
              let f''_, p'_ = init f'_ in
              (f''_, function p -> T.Lam (d_, p'_ p)))
          | f'_ -> (f'_, function p -> p)
        in
        let f'_, pinit_ = init f_ in
        let c_ = traverse (psi0_, l_, statSig, wmap, projs) in
        pinit_ (T.Case (T.Cases (c0_ @ c_)))
      in
      let rec convertPrg' = function
        | [], _ -> raise (Error "Cannot convert Empty program")
        | a :: [], f_ -> convertOnePrg (a, f_)
        | a :: l'_, T.And (f1_, f2_) ->
            T.PairPrg (convertOnePrg (a, f1_), convertPrg' (l'_, f2_))
      in
      let p_ = prec_ (convertPrg' (l_, f0_)) in
      p_

    let rec installFor (cid :: []) =
      let f_ = convertFor [ cid ] in
      let name = I.conDecName (I.sgnLookup cid) in
      let _ = T.lemmaAdd (T.ForDec (name, f_)) in
      ()

    let rec depthConj = function
      | T.And (f1_, f2_) -> 1 + depthConj f2_
      | f_ -> 1

    let rec createProjection = function
      | psi_, depth, (T.And (f1_, f2_) as f_), pattern_ ->
          createProjection
            ( I.Decl (psi_, T.PDec (None, f1_, None, None)),
              depth + 1,
              T.forSub (f2_, T.Shift 1),
              T.PairPrg (T.Var (depth + 2), pattern_) )
      | psi_, depth, f_, pattern_ -> (
          let psi'_ = I.Decl (psi_, T.PDec (None, f_, None, None)) in
          let depth' = depth + 1 in
          function
          | k ->
              let (T.PDec (_, f'_, _, _)) = T.ctxDec (psi'_, k) in
              ( T.Case
                  (T.Cases
                     [
                       (psi'_, T.Dot (T.Prg pattern_, T.Shift depth'), T.Var k);
                     ]),
                f'_ ))

    let rec installProjection = function
      | [], _, f_, proj -> []
      | cid :: cids, n, f_, proj ->
          let p'_, f'_ = proj n in
          let p_ = T.Lam (T.PDec (None, f_, None, None), p'_) in
          let f''_ = T.All ((T.PDec (None, f_, None, None), T.Explicit), f'_) in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (p_, f''_)) in
          let lemma = T.lemmaAdd (T.ValDec ("#" ^ name, p_, f''_)) in
          lemma :: installProjection (cids, n - 1, f_, proj)

    let rec installSelection = function
      | cid :: [], lemma :: [], f1_, main ->
          let p_ = T.Redex (T.Const lemma, T.AppPrg (T.Const main, T.Nil)) in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (p_, f1_)) in
          let lemma' = T.lemmaAdd (T.ValDec (name, p_, f1_)) in
          [ lemma' ]
      | cid :: cids, lemma :: lemmas, T.And (f1_, f2_), main ->
          let p_ = T.Redex (T.Const lemma, T.AppPrg (T.Const main, T.Nil)) in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (p_, f1_)) in
          let lemma' = T.lemmaAdd (T.ValDec (name, p_, f1_)) in
          lemma' :: installSelection (cids, lemmas, f2_, main)

    let rec installPrg = function
      | cid :: [] ->
          let f_ = convertFor [ cid ] in
          let p_ = convertPrg ([ cid ], None) in
          let name = I.conDecName (I.sgnLookup cid) in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (p_, f_)) in
          let _ =
            begin if !Global.chatter >= 4 then
              print "[Redundancy Checker (factoring) ..."
            else ()
            end
          in
          let factP = Converter__0.Redundant.convert p_ in
          let _ =
            begin if !Global.chatter >= 4 then print "done]\n" else ()
            end
          in
          let lemma = T.lemmaAdd (T.ValDec (name, factP, f_)) in
          (lemma, [], [])
      | cids ->
          let f_ = convertFor cids in
          let _ = TomegaTypeCheck.checkFor (I.Null, f_) in
          let proj = createProjection (I.Null, 0, f_, T.Var 1) in
          let projs = installProjection (cids, depthConj f_, f_, proj) in
          let p_ = convertPrg (cids, Some projs) in
          let s = name cids in
          let _ = TomegaTypeCheck.checkPrg (I.Null, (p_, f_)) in
          let _ =
            begin if !Global.chatter >= 4 then
              print "[Redundancy Checker (factoring) ..."
            else ()
            end
          in
          let factP = Converter__0.Redundant.convert p_ in
          let _ =
            begin if !Global.chatter >= 4 then print "done]\n" else ()
            end
          in
          let lemma = T.lemmaAdd (T.ValDec (s, factP, f_)) in
          let sels = installSelection (cids, projs, f_, lemma) in
          (lemma, projs, sels)

    let rec mkResult = function
      | 0 -> T.Unit
      | n -> T.PairExp (I.Root (I.BVar n, I.Nil), mkResult (n - 1))

    let rec convertGoal (g_, v_) =
      let a = I.targetFam v_ in
      let w_ = WorldSyn.lookup a in
      let w'_, wmap = transformWorlds ([ a ], w_) in
      let (Some (_, (p'_, q'_))) =
        traversePos ([], wmap, None)
          ( (I.Null, g_, I.Null),
            v_,
            Some
              ( I.Shift (I.ctxLength g_),
                ( (function p_ -> (I.Null, T.id, p_)),
                  mkResult (I.ctxLength g_) ) ) )
      in
      let _, _, p''_ = p'_ q'_ in
      p''_
  end

  (* ABP - 4/20/03, determine if Front is (I.Idx 1) *)
  (* strengthenExp (U, s) = U'

       Invariant:
       If   G |- s : G'
       and  G |- U : V
       then G' |- U' = U[s^-1] : V [s^-1]
    *)
  (* strengthenDec (x:V, s) = x:V'

       Invariant:
       If   G |- s : G'
       and  G |- V : L
       then G' |- V' = V[s^-1] : L
    *)
  (* G0 |- t : Gsome *)
  (* G0  |- s : G' *)
  (* to show  G' |- t o s^1 : Gsome *)
  (* strengthenCtx (G, s) = (G', s')

       If   G0 |- G ctx
       and  G0 |- w : G1
       then G1 |- G' = G[w^-1] ctx
       and  G0 |- w' : G1, G'
    *)
  (* strengthenFor (F, s) = F'

       If   Psi0 |- F for
       and  Psi0 |- s :: Psi1
       then Psi1 |- F' = F[s^-1] ctx
    *)
  (* strengthenOrder (O, s) = O'

       If   Psi0 |- O order
       and  Psi0 |- s :: Psi1
       then Psi1 |- O' = O[s^-1] ctx
    *)
  (* strengthenTC (TC, s) = TC'

       If   Psi0 |- TC : termination condition
       and  Psi0 |- s :: Psi1
       then Psi1 |- TC' = TC[s^-1] ctx
    *)
  (* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s :: Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' :: Psi1, Psi'
    *)
  (* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)
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
  (* createIH L = (Psi', P', F')

       Invariant:
       If   L is a list of type families
       and  Psi is a context
       then Psi' extends Psi' by declarations in L
       and  F' is the conjunction of the formuals
            that corresponds to each type family in L
       and  Psi' |- P' in F'
    *)
  (* occursInExpN (k, U) = B,

       Invariant:
       If    U in nf
       then  B iff k occurs in U
    *)
  (* | occursInExpN (k, I.FgnExp (cs, ops)) =
         occursInExpN (k, Whnf.normalize (#toInternal(ops) (), I.id)) MERGE Fri Aug 22 23:09:53 2003 --cs *)
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
  (* strengthen (Psi, (a, S), w, m) = (Psi', w')

       This function traverses the spine, and finds
       all variables in a position input/output position m
       (hence strenghten might not be a good name for it, because it is to general.)

       Invariant:
       If   |- Psi ctx
       and  |- Psi1 ctx      where Psi1 is a subcontext of Psi
       and  Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} > type
       and  Psi |- w : Psi1
       and  m mode
       then |- Psi' ctx
       and  Psi |- w' : Psi'
       where Psi' extends Psi1 (but is a subset of Psi?)
    *)
  (* is this ok? -- cs *)
  (* no other cases *)
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
  (* blocks are always used! *)
  (* createSub (Psi, L) = t'

       Invariant:
       If  |- Psi = Psi0, Psi1 ctx
       and Psi0 contains all declarations for invariants in L
       and |Psi0| = n
       and |L| = k
       and n = k + m - 1
       then Psi |- t' = m, m+1 ... n. ^n :  Psi0
    *)
  (*List.length L *)
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
  (* transformConc ((a, S), w) = P

       Invariant:
       If   Sigma (a) = {x1:A1} .. {xn:An} type
       and  Psi |- S : m1{x1:A1} .. mn{xn:An} type > type
       and  Psi |- w : PsiAll
       then P is proof term consisting of all - objects of S,
            defined in PsiAll
    *)
  (* renameExp f U = U'

       Invariant:
       U' = U module application of f to any projectoin contained
       in U.
    *)
  (* traverseNeg (L, wmap, projs)  (Psi0, Psi, V) = ([w', PQ'], L')    [] means optional

           Invariant:
           If   |- Psi0 ctx      (context that contains induction hypotheses)
           and  Psi0 |- Psi ctx  (context of all assumptions)
           and  Psi0, Psi |- V : type
           then L' list of cases
           and  Psi0, Psi |- w' : Psi0, Psi'
           and  PQ'  is a pair that can generate a proof term
        *)
  (* Psi0, Psi |- w : Psi0, Psi' *)
  (* Sigma (a) = Va *)
  (* Psi0, Psi |- S : {G} type > type *)
  (* Psi1 = Psi0, Psi *)
  (* Psi1 |- w0 : Psi0 *)
  (* |- Psi' ctx *)
  (* Psi1 |- w' : Psi' *)
  (* Psi' |- s'' : G+ *)
  (* G |- w'' : G+ *)
  (* T.UDec *)
  (* Psi0 = x1::F1 ... xn::Fn *)
  (* |- Psi0 matches L *)
  (* Psi0, G, B |- V : type *)
  (* Psi0, G, B |- w1 : Psi0, G', B' *)
  (* Psi1 = Psi0, G, B *)
  (* n = |Psi0, G', B'| *)
  (* m = |Psi0| *)
  (* strengthened invariant Psi0 might be empty --cs Fri Apr 11 15:25:32 2003 *)
  (* apply ((S, mS), F')= (S'', F'')

                 Invariant:
                 Psi0, G, B |- S : V >> type
                   (mS is the corresponding mode spine)
                 and  Psi0, G', B |- F'  :: for
                 then Psi0, G', B |- F'' :: for
                 and  Psi0, G', B |- S'' :: F' >> F''
              *)
  (* Psi0, G', B' |- D = x:V' : type *)
  (* Psi0, G', B', x:V' |- F' :: for *)
  (* Psi0, G', B' |- U' : V' *)
  (* Psi0, G', B' |- F'' :: for *)
  (* Psi0, G', B' |- S'' : F' [t'] >> F'' *)
  (* Psi0, G', B' |- U' ; S''
                                                       : all {x:V'} F' >> F'' *)
  (* Psi0, G', B' |- F'' :: for *)
  (* Psi0, G', B' |- S'' :: F' >> F'' *)
  (*T.Var k' *)
  (* was T.Root  -cs Sun Jan  5 23:15:06 2003 *)
  (* Psi0, G', B' |- P'' :: F'' *)
  (* b = |B| = |B'| *)
  (* Psi0, G |- w1' : Psi0, G' *)
  (* |- Psi0, G', B' ctx *)
  (* n' = |Psi0, G'| *)
  (* Psi0, G' |- GB' ctx *)
  (* Psi0, G, B |- w1 : Psi0, G', B' *)
  (* Psi0, G', GB'  |- s' : Psi0, G', B' *)
  (* Psi0, G', GB' |- RR for *)
  (* Psi0, G |- w1' : Psi0, G' *)
  (* Psi0, G' |- F''' for *)
  (* lift (B, (P, F)) = (P', F')

                 Invariant:
                 If   Psi0, G, B |- P :: F
                 then Psi0, G |- P'  :: F'
                 and  P' =  (lam B. P)
                 and  F' = raiseFor (B, F)
              *)
  (* Psi0, G' |- P''' :: F''' *)
  (* |- Psi0, Psi1'' ctx *)
  (* Psi0, G, B |- w2 : Psi1'' *)
  (* Psi1'' = Psi0, G3, B3' *)
  (* |B| = |GB'| *)
  (* Psi'' |-  z2 : Psi0, G', B' *)
  (* Psi0, G, B |- w2 : Psi0, G3, B3' *)
  (* Psi0, G |- w3 : Psi0, G3 *)
  (* Psi0, G3 |-  z3 : Psi0, G' *)
  (* Psi2 = Psi0, G3 *)
  (* Psi0, G3, B3' |- Pat' :: For *)
  (* Psi0, G3 |- F4 for *)
  (* ' F4 *)
  (* Psi0, G3 |- Pat :: F4  *)
  (* Here's a commutative diagram
                                           at work which one has to prove
                                           correct
                                        *)
  (* Psi0, G3 |- t :: Psi0, G', x :: F4  *)
  (* traverse (Psi0, L, Sig, wmap) = C'

       Invariant:
       If   |- Psi0  ctx
       and  L is a the theorem we would like to transform
       and  Sig is a signature
       and  forall (G, V) in Sig the following holds:
                    Psi0, G |- V : type
               and  head (V) in L
       and  wmap is a mapping of old labels L to L'
            where L' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (L) = (Gsome, Lblock)
            and  Sig (L') = (Gsome, Lblock')
       then C' is a list of cases (corresponding to each (G, V) in Sig)
    *)
  (* transformWorlds (fams, W) = (W', wmap)

       Invariant:
       If   fams is the theorem to be compiled
       and  W a world with declarations,
       then W' is the new world stripped of all dynamic extensions
       and  wmap is a mapping of old labels L to L'
            where L' is a new label and w' is a weakensub
            with the following properties.
            If   Sig (L) = (Gsome, Lblock)
            and  Sig (L') = (Gsome, Lblock')
    *)
  (* convertList (a, L, w) = L'

             Invariant:
             If   G0 |- G, L : ctx
             and  G0, G |- w : G0, G'
             then G0 |- G', L' ctx
          *)
  (* Design decision: Let's keep all of G *)
  (* dynamicSig (Psi0, fams, W) = Sig'

       Invariant:
       If   |- Psi0 ctx
       and  fams are the typfamilies to be converted
       and  W is the world in which the translation takes place
       then Sig' = (G1;V1) ... (Gn;Vn)
       and  |- Psi0, Gi ctx
       and  Psi, Gi |- Vi : type.
    *)
  (* findDec (G, n, L, s, S) = S'

             Invariant:
             If   G |-  L : ctx
             and  G |- w: G'
             then |- G', L' ctx
          *)
  (* mediateSub G = (G0, s)

             Invariant:
             If   . |- G ctx
             then Psi0 |- G0 ctx
             and  Psi0, G0 |- s : G
          *)
  (* G |- L ctx *)
  (* Psi0, G0 |- s'' : G *)
  (* Psi0, G0 |- D : dec *)
  (* Psi0, G0, D' |- s'' : G *)
  (* staticSig Sig = Sig'

       Invariant:
       If   |- Psi0 ctx
       then Sig' = (c1:V1) ... (cn:Vn)
       and  . |- Vi : type.
    *)
  (* convertPrg L = P'

       Invariant:
       If   L is a list of type families
       then P' is a conjunction of all programs resulting from converting
            the relational encoding of the function expressed by each type
            family in L into functional form
    *)
  (* W describes the world of a *)
  (* W describes the world of a *)
  (* Psi0 |- {x1:V1} ... {xn:Vn} type *)
  (* |- mS : {x1:V1} ... {xn:Vn} > type *)
  (* Sig in LF(reg)   *)
  (* init' F = P'

               Invariant:
               If   F = All x1:A1. ... All xn:An. F'
               and  f' does not start with a universal quantifier
               then P' P'' = Lam x1:A1. ... Lam xn:An P''
                    for any P''
            *)
  (* Psi0, x1:V1, ..., xn:Vn |- C :: F *)
  (* F', *)
  let convertFor = convertFor
  let convertPrg = function l_ -> convertPrg (l_, None)
  let installFor = installFor
  let installPrg = installPrg
  let traverse = traverse
  let convertGoal = convertGoal
end
(* functor FunSyn *)

(* # 1 "src/tomega/converter.sml.ml" *)
