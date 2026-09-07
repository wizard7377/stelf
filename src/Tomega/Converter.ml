open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Worldcheck
open! Names.Names_
open! Print.Print_
open! Typecheck
open! Modes

(* # 1 "src/tomega/Converter.sig.ml" *)
module Tomega = Lambda_.Tomega

(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)
include CONVERTER
(* Signature CONVERTER *)

(* # 1 "src/tomega/Converter.fun.ml" *)
open! Basis

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

exception Error' of Tomega.sub

let () =
  Printexc.register_printer (function
    | Error' _ -> Some "Tomega converter error"
    | _ -> None)

module MakeConverter
    (Global : GLOBAL)
    (Abstract : ABSTRACT)
    (ModeTable : Modetable.MODETABLE)
    (Names : NAMES)
    (Unify : UNIFY)
    (Whnf : WHNF)
    (Print : PRINT)
    (TomegaPrint : Tomegaprint.TOMEGAPRINT)
    (WorldSyn : Worldcheck_.WORLDSYN)
    (Worldify : Worldcheck_.WORLDIFY)
    (TomegaTypeCheck : TOMEGATYPECHECK.TOMEGATYPECHECK)
    (Subordinate : Subordinate.Subordinate_.SUBORDINATE)
    (TypeCheck : Typecheck_.TYPECHECK)
    (Redundant : REDUNDANT.REDUNDANT)
    (TomegaAbstract : TOMEGAABSTRACT.TOMEGAABSTRACT) : CONVERTER = struct
  (*
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
  module Worldify : Worldcheck_.WORLDIFY

  (*! sharing Worldify.IntSyn = IntSyn' !*)
  (*! sharing Worldify.Tomega = Tomega' !*)
  module TomegaTypeCheck : TOMEGATYPECHECK.TOMEGATYPECHECK

  (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
  (*! sharing TomegaTypeCheck.Tomega = Tomega' !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module TypeCheck : Typecheck_.TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Redundant : REDUNDANT.REDUNDANT
  module TomegaAbstract : TOMEGAABSTRACT.TOMEGAABSTRACT
*)
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  exception Error = Error
  exception Error' = Error'

  open! struct
    module T = Tomega
    module I = IntSyn
    module M = Modes.Modesyn.ModeSyn
    module S = Subordinate
    module A = Abstract
    module TomegaTypeCheck = TomegaTypeCheck
    module TA = TomegaAbstract

    let isIdx1 = function I.Idx 1 -> true | _ -> false

    let modeSpine a =
      begin match ModeTable.modeLookup a with
      | None -> raise (Error "Mode declaration expected")
      | Some mS -> mS
      end

    let typeOf a =
      begin match I.sgnLookup a with
      | I.ConDec (name, _, _, _, v, I.Kind) -> v
      | _ -> raise (Error "Type Constant declaration expected")
      end

    let nameOf a =
      begin match I.sgnLookup a with
      | I.ConDec (name, _, _, _, v, I.Kind) -> name
      | _ -> raise (Error "Type Constant declaration expected")
      end

    let chatter chlev f = Display.chatter_s chlev ("[tomega] " ^ f ())
    let strengthenExp u s = Whnf.normalize (Whnf.cloInv u s, I.id)
    let strengthenSub s t = Whnf.compInv s t

    let strengthenDec a1 b1 = match a1, b1 with
      | I.Dec (name, v), s -> I.Dec (name, strengthenExp v s)
      | I.BDec (name, (l, t)), s -> I.BDec (name, (l, strengthenSub t s))

    let rec strengthenCtx a1 b1 = match a1, b1 with
      | I.Null, s -> (I.Null, s)
      | I.Decl (g, d), s ->
          let g', s' = strengthenCtx g s in
          (I.Decl (g', strengthenDec d s'), I.dot1 s')

    let rec strengthenFor (a, s) = match a with
      | T.True -> T.True
      | T.And (f1, f2) ->
          T.And (strengthenFor (f1, s), strengthenFor (f2, s))
      | T.All ((T.UDec d, q), f) ->
          T.All
            ((T.UDec (strengthenDec d s), q), strengthenFor (f, I.dot1 s))
      | T.Ex ((d, q), f) ->
          T.Ex ((strengthenDec d s, q), strengthenFor (f, I.dot1 s))

    let rec strengthenOrder (a, s) = match a with
      | Intsyn.Order.Arg ((u, s1), (v, s2)) ->
          Intsyn.Order.Arg
            ((u, strengthenSub s1 s), (v, strengthenSub s2 s))
      | Intsyn.Order.Simul os ->
          Intsyn.Order.Simul
            (map (function o -> strengthenOrder (o, s)) os)
      | Intsyn.Order.Lex os ->
          Intsyn.Order.Lex (map (function o -> strengthenOrder (o, s)) os)

    let rec strengthenTC (a, s) = match a with
      | T.Base o -> T.Base (strengthenOrder (o, s))
      | T.Conj (tc1, tc2) ->
          T.Conj (strengthenTC (tc1, s), strengthenTC (tc2, s))
      | T.Abs (d, tc) ->
          T.Abs (strengthenDec d s, strengthenTC (tc, I.dot1 s))

    let rec strengthenSpine a1 b1 = match a1, b1 with
      | I.Nil, t -> I.Nil
      | I.App (u, s), t ->
          I.App (strengthenExp u t, strengthenSpine s t)

    let rec strengthenPsi a1 b1 = match a1, b1 with
      | I.Null, s -> (I.Null, s)
      | I.Decl (psi, T.UDec d), s ->
          let psi', s' = strengthenPsi psi s in
          (I.Decl (psi', T.UDec (strengthenDec d s')), I.dot1 s')
      | I.Decl (psi, T.PDec (name, f, None, None)), s ->
          let psi', s' = strengthenPsi psi s in
          ( I.Decl (psi', T.PDec (name, strengthenFor (f, s'), None, None)),
            I.dot1 s' )

    let rec strengthenPsi' a1 b1 = match a1, b1 with
      | [], s -> ([], s)
      | T.UDec d :: psi, s ->
          let d' = strengthenDec d s in
          let s' = I.dot1 s in
          let psi'', s'' = strengthenPsi' psi s' in
          (T.UDec d' :: psi'', s'')

    let rec ctxSub (a, s) = match a with
      | I.Null -> (I.Null, s)
      | I.Decl (g, d) ->
          let g', s' = ctxSub (g, s) in
          (I.Decl (g', I.decSub d s'), I.dot1 s)

    let rec validMode = function
      | M.Mnil -> ()
      | M.Mapp (M.Marg (M.Plus, _), mS) -> validMode mS
      | M.Mapp (M.Marg (M.Minus, _), mS) -> validMode mS
      | M.Mapp (M.Marg (M.Star, _), mS) ->
          raise (Error "+ or - mode expected, * found")

    let rec validSig (psi0, a) = match a with
      | [] -> ()
      | (g, v) :: sig_ ->
          let rec append (g, a) = match a with
            | I.Null -> g
            | I.Decl (g', d) -> I.Decl (append (g, g'), d)
          in
          TypeCheck.typeCheck
            (T.coerceCtx (append (psi0, T.embedCtx g))) (v, I.Uni I.Type);
          validSig (psi0, sig_)

    let convertOneFor cid =
      let v =
        begin match I.sgnLookup cid with
        | I.ConDec (name, _, _, _, v, I.Kind) -> v
        | _ -> raise (Error "Type Constant declaration expected")
        end
      in
      let mS =
        begin match ModeTable.modeLookup cid with
        | None -> raise (Error "Mode declaration expected")
        | Some mS -> mS
        end
      in
      ignore (validMode mS);
      let rec convertFor' = function
        | I.Pi ((d, _), v), M.Mapp (M.Marg (M.Plus, _), mS), w1, w2, n ->
            let f', f'' =
              convertFor' (v, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n - 1)
            in
            ( (function
              | f ->
                  T.All ((T.UDec (strengthenDec d w1), T.Explicit), f' f)),
              f'' )
        | I.Pi ((d, _), v), M.Mapp (M.Marg (M.Minus, _), mS), w1, w2, n ->
            let f', f'' =
              convertFor' (v, mS, I.comp w1 I.shift, I.dot1 w2, n + 1)
            in
            (f', T.Ex ((I.decSub d w2, T.Explicit), f''))
        | I.Uni I.Type, M.Mnil, _, _, _ -> ((function f -> f), T.True)
        | _ -> raise (Error "type family must be +/- moded")
      in
      let shiftPlus mS =
        let rec shiftPlus' (a, n) = match a with
          | M.Mnil -> n
          | M.Mapp (M.Marg (M.Plus, _), mS') -> shiftPlus' (mS', n + 1)
          | M.Mapp (M.Marg (M.Minus, _), mS') -> shiftPlus' (mS', n)
        in
        shiftPlus' (mS, 0)
      in
      let n = shiftPlus mS in
      let f, f' = convertFor' (v, mS, I.id, I.Shift n, n) in
      f f'

    let rec createIH = function
      | [] -> raise (Error "Empty theorem")
      | a :: [] ->
          let name = I.conDecName (I.sgnLookup a) in
          let f = convertOneFor a in
          (name, f)
      | a :: l ->
          let name = I.conDecName (I.sgnLookup a) in
          let f = convertOneFor a in
          let name', f' = createIH l in
          ((name ^ "/") ^ name', T.And (f, f'))

    let convertFor l =
      let _, f' = createIH l in
      f'

    let rec occursInExpN (k, a) = match a with
      | I.Uni _ -> false
      | I.Pi (dp, v) -> occursInDecP (k, dp) || occursInExpN (k + 1, v)
      | I.Root (h, s) -> occursInHead (k, h) || occursInSpine (k, s)
      | I.Lam (d, v) -> occursInDec (k, d) || occursInExpN (k + 1, v)
      | I.FgnExp (csid, csfe) ->
          I.FgnExpStd.fold csid csfe
            (function
              | u, dp -> dp || occursInExp (k, Whnf.normalize (u, I.id)))
            false

    and occursInHead (k, a) = match a with
      | I.BVar k' -> k = k'
      | I.Const _ -> false
      | I.Def _ -> false
      | I.FgnConst _ -> false
      | I.Proj _ -> false

    and occursInSpine (k, a) = match a with
      | I.Nil -> false
      | I.App (u, s) -> occursInExpN (k, u) || occursInSpine (k, s)

    and occursInDec (k, I.Dec (_, v)) = occursInExpN (k, v)
    and occursInDecP (k, (d, _)) = occursInDec (k, d)
    and occursInExp (k, u) = occursInExpN (k, Whnf.normalize (u, I.id))

    let dot1inv w = strengthenSub (I.comp I.shift w) I.shift
    let shiftinv w = strengthenSub w I.shift

    let peel w =
      begin if isIdx1 (I.bvarSub 1 w) then dot1inv w else shiftinv w
      end

    let rec peeln (n, w) = match n with 0 -> w | n -> peeln (n - 1, peel w)

    let rec popn = function
      | 0, psi -> (psi, I.Null)
      | n, I.Decl (psi, T.UDec d) ->
          let psi', g' = popn (n - 1, psi) in
          (psi', I.Decl (g', d))

    let rec domain = function
      | g, I.Dot (I.Idx _, s) -> domain (g, s) + 1
      | I.Null, I.Shift 0 -> 0
      | (I.Decl _ as g), I.Shift 0 -> domain (g, I.Dot (I.Idx 1, I.Shift 1))
      | I.Decl (g, _), I.Shift n -> domain (g, I.Shift (n - 1))

    let strengthen (psi, (a, s_), w, m) =
      let mS = modeSpine a in
      let rec args = function
        | I.Nil, M.Mnil -> []
        | I.App (u, s'), M.Mapp (M.Marg (m', _), mS) ->
            let l = args (s', mS) in
            if M.modeEqual m m' then u :: l else l
      in
      let rec strengthenArgs (a, s) = match a with
        | [] -> []
        | u :: l -> strengthenExp u s :: strengthenArgs (l, s)
      in
      let rec occursInArgs (n, a) = match a with
        | [] -> false
        | u :: l -> occursInExp (n, u) || occursInArgs (n, l)
      in
      let rec occursInPsi (n, a) = match a with
        | ([], l) -> occursInArgs (n, l)
        | (T.UDec (I.Dec (_, v)) :: psi1, l) ->
            occursInExp (n, v) || occursInPsi (n + 1, (psi1, l))
        | (T.UDec (I.BDec (_, (cid, s))) :: psi1, l) ->
            let (I.BlockDec (_, _, g, _)) = I.sgnLookup cid in
            occursInSub (n, s, g) || occursInPsi (n + 1, (psi1, l))
      and occursInSub (n, a, b) = match a, b with
        | _, I.Null -> false
        | I.Shift k, g ->
            occursInSub (n, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), g)
        | I.Dot (I.Idx k, s), I.Decl (g, _) ->
            n = k || occursInSub (n, s, g)
        | I.Dot (I.Exp u, s), I.Decl (g, _) ->
            occursInExp (n, u) || occursInSub (n, s, g)
        | I.Dot (I.Block _, s), I.Decl (g, _) -> occursInSub (n, s, g)
      and occursInG (n, a, k) = match a with
        | I.Null -> k n
        | I.Decl (g, I.Dec (_, v)) ->
            occursInG
              (n, g, function n' -> occursInExp (n', v) || k (n' + 1))
      in
      let occursBlock (g, (psi2, l)) =
        let rec occursBlock (a, n) = match a with
          | I.Null -> false
          | I.Decl (g, d) ->
              occursInPsi (n, (psi2, l)) || occursBlock (g, n + 1)
        in
        occursBlock (g, 1)
      in
      let rec inBlock = function
        | I.Null, (bw, w1) -> (bw, w1)
        | I.Decl (g, d), (bw, w1) ->
            begin if isIdx1 (I.bvarSub 1 w1) then
              inBlock (g, (true, dot1inv w1))
            else inBlock (g, (bw, strengthenSub w1 I.shift))
            end
      in
      let rec blockSub a1 b1 = match a1, b1 with
        | I.Null, w -> (I.Null, w)
        | I.Decl (g, I.Dec (name, v)), w ->
            let g', w' = blockSub g w in
            let v' = strengthenExp v w' in
            (I.Decl (g', I.Dec (name, v')), I.dot1 w')
      in
      let rec strengthen' (a, psi2, l, w1) = match a with
        | I.Null -> (I.Null, I.id, I.id)
        | I.Decl (psi1, (T.UDec (I.Dec (name, v)) as ld)) ->
            begin if isIdx1 (I.bvarSub 1 w1) then
              let w1' = dot1inv w1 in
              let psi1', w', z' = strengthen' (psi1, ld :: psi2, l, w1') in
              let v' = strengthenExp v w' in
              (I.Decl (psi1', T.UDec (I.Dec (name, v'))), I.dot1 w', I.dot1 z')
            else
              begin if occursInPsi (1, (psi2, l)) then
                let w1' = strengthenSub w1 I.shift in
                let psi1', w', z' = strengthen' (psi1, ld :: psi2, l, w1') in
                let v' = strengthenExp v w' in
                ( I.Decl (psi1', T.UDec (I.Dec (name, v'))),
                  I.dot1 w',
                  I.comp z' I.shift )
              else
                let w1' = strengthenSub w1 I.shift in
                let w2 = I.shift in
                let psi2', w2' = strengthenPsi' psi2 w2 in
                let l' = strengthenArgs (l, w2') in
                let psi1'', w', z' = strengthen' (psi1, psi2', l', w1') in
                (psi1'', I.comp w' I.shift, z')
              end
            end
        | I.Decl (psi1, (T.PDec (name, f, None, None) as d)) ->
            let w1' = dot1inv w1 in
            let psi1', w', z' = strengthen' (psi1, d :: psi2, l, w1') in
            let f' = strengthenFor (f, w') in
            ( I.Decl (psi1', T.PDec (name, f', None, None)),
              I.dot1 w',
              I.dot1 z' )
        | I.Decl (psi1, (T.UDec (I.BDec (name, (cid, s))) as ld))
          ->
            let w1' = dot1inv w1 in
            let psi1', w', z' = strengthen' (psi1, ld :: psi2, l, w1') in
            let s' = strengthenSub s w' in
            ( I.Decl (psi1', T.UDec (I.BDec (name, (cid, s')))),
              I.dot1 w',
              I.dot1 z' )
      in
      strengthen' (psi, [], args (s_, mS), w)

    let lookupIH (psi, l, a) =
      let rec lookupIH' (b :: l, a, k) =
        begin if a = b then k else lookupIH' (l, a, k - 1)
        end
      in
      lookupIH' (l, a, I.ctxLength psi)

    let createIHSub (psi, l) = T.Shift (I.ctxLength psi - 1)

    let transformInit (psi, l, (a, s_), w1) =
      let mS = modeSpine a in
      let v = typeOf a in
      let rec transformInit' = function
        | (I.Nil, M.Mnil), I.Uni I.Type, (w, s) -> (w, s)
        | ( (I.App (u, s_), M.Mapp (M.Marg (M.Minus, _), mS)),
            I.Pi (_, v2),
            (w, s) ) ->
            let w' = I.comp w I.shift in
            let s' = s in
            transformInit' ((s_, mS), v2, (w', s'))
        | ( (I.App (u, s_), M.Mapp (M.Marg (M.Plus, _), mS)),
            I.Pi ((I.Dec (name, v1), _), v2),
            (w, s) ) ->
            let v1' = strengthenExp v1 w in
            let w' = I.dot1 w in
            let u' = strengthenExp u w1 in
            let s' = T.dotEta (T.Exp u') s in
            transformInit' ((s_, mS), v2, (w', s'))
      in
      transformInit' ((s_, mS), v, (I.id, createIHSub (psi, l)))

    let transformConc ((a, s), w) =
      let rec transformConc' = function
        | I.Nil, M.Mnil -> T.Unit
        | I.App (u, s'), M.Mapp (M.Marg (M.Plus, _), mS') ->
            transformConc' (s', mS')
        | I.App (u, s'), M.Mapp (M.Marg (M.Minus, _), mS') ->
            T.PairExp (strengthenExp u w, transformConc' (s', mS'))
      in
      transformConc' (s, modeSpine a)

    let rec renameExp arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | f, (I.Uni _ as u) -> u
      | f, I.Pi ((d, dp), v) -> I.Pi ((renameDec f d, dp), renameExp f v)
      | f, I.Root (h, s) -> I.Root (renameHead f h, renameSpine f s)
      | f, I.Lam (d, u) -> I.Lam (renameDec f d, renameExp f u)
      end

    and renameDec f (I.Dec (x, v)) = I.Dec (x, renameExp f v)

    and renameHead arg__3 arg__4 =
      begin match (arg__3, arg__4) with
      | f, I.Proj (bi, i) -> f (bi, i)
      | f, h -> h
      end

    and renameSpine arg__5 arg__6 =
      begin match (arg__5, arg__6) with
      | f, I.Nil -> I.Nil
      | f, I.App (u, s) -> I.App (renameExp f u, renameSpine f s)
      end

    let rename (I.BDec (_, (c, s))) v =
      let g, l = I.constBlock c in
      let rec makeSubst (n, g, s, a, f) = match a with
        | [] -> (g, f)
        | (I.Dec (x, v') as d) :: l ->
            begin if S.belowEq (I.targetFam v') (I.targetFam v) then
              makeSubst (n + 1, I.Decl (g, I.decSub d s), I.dot1 s, l, f)
            else makeSubst (n, g, I.comp s I.shift, l, f)
            end
      in
      let g', f = makeSubst (1, g, s, l, function x, i -> I.Proj (x, i)) in
      (g, renameExp f v)

    let rec append (g, a) = match a with
      | I.Null -> g
      | I.Decl (g', d) -> I.Decl (append (g, g'), d)

    let rec traverseNeg arg__7 arg__8 =
      begin match (arg__7, arg__8) with
      | ( (l, wmap, projs),
          ((psi0, psi), I.Pi (((I.Dec (_, v1) as d), Maybe), v2), w) ) ->
          begin match
            traverseNeg (l, wmap, projs)
              ((psi0, I.Decl (psi, T.UDec d)), v2, I.dot1 w)
          with
          | Some (w', pq') -> Some (peel w', pq')
          end
      | ( (l, wmap, projs),
          ((psi0, psi), I.Pi (((I.Dec (_, v1) as d), No), v2), w) ) ->
          begin match
            traverseNeg (l, wmap, projs)
              ((psi0, I.Decl (psi, T.UDec d)), v2, I.comp w I.shift)
          with
          | Some (w', pq') ->
              traversePos (l, wmap, projs)
                ((psi0, psi, I.Null), v1, Some (peel w', pq'))
          end
      | (l, wmap, projs), ((psi0, psi), I.Root (I.Const a, s), w) ->
          let psi1 = append (psi0, psi) in
          let w0 = I.Shift (I.ctxLength psi) in
          let psi', w', _ = strengthen (psi1, (a, s), w0, M.Plus) in
          let w'', s'' = transformInit (psi', l, (a, s), w') in
          ignore (TomegaTypeCheck.checkCtx psi');
          Some
            ( w',
              ((function p -> (psi', s'', p)), transformConc ((a, s), w)) )
      end

    and traversePos arg__9 arg__10 =
      begin match (arg__9, arg__10) with
      | ( (l, wmap, projs),
          ( (psi0, psi, g),
            I.Pi (((I.BDec (x, (c, s)) as d), _), v),
            Some (w1, (p, q)) ) ) ->
          let c' = wmap c in
          let n = I.ctxLength psi0 + I.ctxLength g in
          let gsome, lpi = I.constBlock c in
          ignore (TypeCheck.typeCheckCtx
              (T.coerceCtx (append (append (psi0, psi), T.embedCtx g))));
          ignore (TypeCheck.typeCheckSub
              (T.coerceCtx (append (append (psi0, psi), T.embedCtx g))) s gsome);
          let gsome', lpi' = I.constBlock c' in
          ignore (TypeCheck.typeCheckCtx
              (T.coerceCtx (append (append (psi0, psi), T.embedCtx g))));
          ignore (TypeCheck.typeCheckSub
              (T.coerceCtx (append (append (psi0, psi), T.embedCtx g))) s gsome');
          traversePos (l, wmap, projs)
            ( (psi0, psi, I.Decl (g, I.BDec (x, (c', s)))),
              v,
              Some (I.dot1 w1, (p, q)) )
      | ( (l_, wmap, projs),
          ((psi0, g, b_), (I.Root (I.Const a, s_) as v), Some (w1, (p_, q)))
        ) ->
          let psi1 = append (psi0, append (g, T.embedCtx b_)) in
          ignore (TomegaTypeCheck.checkCtx (append (append (psi0, g), T.embedCtx b_)));
          let n = domain (psi1, w1) in
          let m = I.ctxLength psi0 in
          let lookupbase a =
            let s = I.conDecName (I.sgnLookup a) in
            let l = T.lemmaName s in
            let (T.ValDec (_, p, f)) = T.lemmaLookup l in
            (T.Const l, f)
          in
          let rec lookup (c, a) = match c with
            | (b :: [], None, f) ->
                begin if a = b then
                  let p = T.Var n in
                  (p, f)
                else lookupbase a
                end
            | (b :: [], Some (lemma :: []), f) ->
                begin if a = b then
                  let p = T.Redex (T.Const lemma, T.AppPrg (T.Var n, T.Nil)) in
                  (p, f)
                else lookupbase a
                end
            | (b :: l, Some (lemma :: lemmas), T.And (f1, f2)) ->
                begin if a = b then
                  let p = T.Redex (T.Const lemma, T.AppPrg (T.Var n, T.Nil)) in
                  (p, f1)
                else lookup ((l, Some lemmas, f2), a)
                end
          in
          let hp, f =
            begin if I.ctxLength psi0 > 0 then
              let (T.PDec (_, f0, _, _)) = I.ctxLookup psi0 1 in
              lookup ((l_, projs, f0), a)
            else lookupbase a
            end
          in
          let rec apply (s, mS) (f, t) = applyW ((s, mS), T.whnfFor f t)
          and applyW = function
            | (I.Nil, M.Mnil), ft' -> (T.Nil, (let f__, t__ = ft' in T.forSub f__ t__))
            | ( (I.App (u, s), M.Mapp (M.Marg (M.Plus, _), mS)),
                (T.All (d, f'), t') ) ->
                let u' = strengthenExp u w1 in
                let s'', f'' =
                  apply (s, mS) (f', T.Dot (T.Exp u', t'))
                in
                (T.AppExp (u', s''), f'')
            | (I.App (u, s), M.Mapp (M.Marg (M.Minus, _), mS)), ft ->
                applyW ((s, mS), ft)
          in
          let s'', f'' = apply (s_, modeSpine a) (f, T.id) in
          ignore (TomegaTypeCheck.checkFor
              (append (append (psi0, g), T.embedCtx b_)) (T.forSub f'' (T.embedSub w1)));
          let p'' = T.Redex (hp, s'') in
          let b = I.ctxLength b_ in
          let w1' = peeln (b, w1) in
          let b', _ = strengthenCtx b_ w1' in
          let n' = n - I.ctxLength b' in
          let rec subCtx (a, s) = match a with
            | I.Null -> (I.Null, s)
            | I.Decl (g, d) ->
                let g', s' = subCtx (g, s) in
                (I.Decl (g', I.decSub d s'), I.dot1 s')
          in
          let b'', _ = subCtx (b', w1') in
          ignore (TomegaTypeCheck.checkCtx
              (append (append (psi0, g), T.embedCtx b'')));
          let gb', iota = T.deblockify b' in
          ignore (try TypeCheck.typeCheckSub gb' (T.coerceSub iota) b'
            with TypeCheck.Error _ -> raise (Error' iota));
          let rr = T.forSub f'' iota in
          let f''' = TA.raiseFor gb' (rr, I.id) in
          let rec lift (a, p) = match a with
            | I.Null -> p
            | I.Decl (g, d) ->
                let bint, _ = T.deblockify (I.Decl (I.Null, d)) in
                lift (g, T.New (T.Lam (T.UDec d, p)))
          in
          let p''' = lift (b', p'') in
          ignore (TomegaTypeCheck.checkCtx (append (psi0, g)));
          ignore (TomegaTypeCheck.checkFor
              (append (psi0, g)) (T.forSub f''' (T.embedSub w1')));
          let psi1'', w2, z2 = strengthen (psi1, (a, s_), w1, M.Minus) in
          let w3 = peeln (b, w2) in
          let z3 = peeln (b, z2) in
          let psi2, b3' = popn (b, psi1'') in
          let pat' = transformConc ((a, s_), w2) in
          let f4 = T.forSub f''' (T.embedSub z3) in
          ignore (TomegaTypeCheck.checkCtx psi1'');
          ignore (TomegaTypeCheck.checkCtx (append (psi2, T.embedCtx b3')));
          ignore (try TomegaTypeCheck.checkFor psi2 f4
            with _ -> raise (Error ""));
          let b3, sigma3 = T.deblockify b3' in
          let pat'' = T.normalizePrg pat' sigma3 in
          let pat = TA.raisePrg b3 pat'' f4 in
          ignore (TomegaTypeCheck.checkPrg psi2 (pat, f4));
          let t = T.Dot (T.Prg pat, T.embedSub z3) in
          Some
            ( w3,
              ( (function
                | p ->
                    p_
                      (T.Let
                         ( T.PDec (None, f''', None, None),
                           p''',
                           T.Case (T.Cases [ (psi2, t, p) ]) ))),
                q ) )
      end

    let traverse (psi0, l, sig_, wmap, projs) =
      let rec traverseSig' = function
        | [] -> []
        | (g, v) :: sig_ -> begin
            TypeCheck.typeCheck
              (append (T.coerceCtx psi0, g)) (v, I.Uni I.Type);
            begin match
              traverseNeg (l, wmap, projs) ((psi0, T.embedCtx g), v, I.id)
            with
            | Some (wf, (p', q')) -> traverseSig' sig_ @ [ p' q' ]
            end
          end
      in
      traverseSig' sig_

    let transformWorlds (fams, T.Worlds cids) =
      let rec transformList (c, w) = match c with
        | [] -> []
        | (I.Dec (x, v) as d) :: l ->
            begin if
              List.foldr
                (function a, b -> b && S.belowEq a (I.targetFam v))
                true fams
            then transformList (l, I.comp w I.shift)
            else
              let l' = transformList (l, I.dot1 w) in
              I.Dec (x, strengthenExp v w) :: l'
            end
      in
      let rec transformWorlds' = function
        | [] -> ([], function c -> raise (Error "World not found"))
        | cid :: cids' -> (
            let (I.BlockDec (s, m, g, l)) = I.sgnLookup cid in
            let l' = transformList (l, I.id) in
            let cids'', wmap = transformWorlds' cids' in
            let cid' = I.sgnAdd (I.BlockDec (s, m, g, l')) in
            ( cid' :: cids'',
              function
              | c ->
                  begin if c = cid then cid' else wmap c
                  end ))
      in
      let cids', wmap = transformWorlds' cids in
      (T.Worlds cids', wmap)

    let dynamicSig (psi0, a, T.Worlds cids) =
      let rec findDec (g, n, c, w, sig_) = match c with
        | [] -> sig_
        | d :: l ->
            let (I.Dec (x, v') as d') = I.decSub d w in
            let b = I.targetFam v' in
            let sig' =
              begin if b = a then (g, Whnf.normalize (v', I.id)) :: sig_
              else sig_
              end
            in
            findDec
              ( g,
                n + 1,
                l,
                I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, n), I.Nil)), w),
                sig' )
      in
      let rec mediateSub = function
        | I.Null -> (I.Null, I.Shift (I.ctxLength psi0))
        | I.Decl (g, d) ->
            let g0, s' = mediateSub g in
            let d' = I.decSub d s' in
            (I.Decl (g0, d'), I.dot1 s')
      in
      let rec findDecs' (a, sig_) = match a with
        | [] -> sig_
        | cid :: cids' ->
            let (I.BlockDec (s, m, g, l)) = I.sgnLookup cid in
            let g0, s' = mediateSub g in
            let d' = Names.decName g0 (I.BDec (None, (cid, s'))) in
            let s'' = I.comp s' I.shift in
            let sig' = findDec (I.Decl (g0, d'), 1, l, s'', sig_) in
            findDecs' (cids', sig')
      in
      findDecs' (cids, [])

    let rec staticSig (psi0, a) = match a with
      | [] -> []
      | I.ConDec (name, _, _, _, v, I.Type) :: sig_ ->
          (I.Null, Whnf.normalize (v, I.Shift (I.ctxLength psi0)))
          :: staticSig (psi0, sig_)

    let rec name = function
      | a :: [] -> I.conDecName (I.sgnLookup a)
      | a :: l -> (I.conDecName (I.sgnLookup a) ^ "/") ^ name l

    let convertPrg (l, projs) =
      let name, f0 = createIH l in
      let d0 = T.PDec (Some name, f0, None, None) in
      let psi0 = I.Decl (I.Null, d0) in
      let prec p = T.Rec (d0, p) in
      let rec convertWorlds = function
        | a :: [] ->
            let w = WorldSyn.lookup a in
            w
        | a :: l' ->
            let w = WorldSyn.lookup a in
            let w' = convertWorlds l' in
            begin if T.eqWorlds w w' then w'
            else raise (Error "Type families different in different worlds")
            end
      in
      let w = convertWorlds l in
      let w', wmap = transformWorlds (l, w) in
      let convertOnePrg (a, f) =
        let name = nameOf a in
        let v = typeOf a in
        let mS = modeSpine a in
        let sig_ = Worldify.worldify a in
        let dynSig = dynamicSig (psi0, a, w) in
        let statSig = staticSig (psi0, sig_) in
        ignore (map
            (function
              | I.ConDec (_, _, _, _, u, v) -> TypeCheck.check (u, I.Uni v))
            sig_);
        ignore (validSig (psi0, statSig));
        ignore (validSig (psi0, dynSig));
        let c0 = traverse (psi0, l, dynSig, wmap, projs) in
        let rec init = function
          | T.All ((d, _), f') -> (
              let f'', p' = init f' in
              (f'', function p -> T.Lam (d, p' p)))
          | f' -> (f', function p -> p)
        in
        let f', pinit = init f in
        let c = traverse (psi0, l, statSig, wmap, projs) in
        pinit (T.Case (T.Cases (c0 @ c)))
      in
      let rec convertPrg' = function
        | [], _ -> raise (Error "Cannot convert Empty program")
        | a :: [], f -> convertOnePrg (a, f)
        | a :: l', T.And (f1, f2) ->
            T.PairPrg (convertOnePrg (a, f1), convertPrg' (l', f2))
      in
      let p = prec (convertPrg' (l, f0)) in
      p

    let installFor (cid :: []) =
      let f = convertFor [ cid ] in
      let name = I.conDecName (I.sgnLookup cid) in
      ignore (T.lemmaAdd (T.ForDec (name, f)));
      ()

    let rec depthConj = function
      | T.And (f1, f2) -> 1 + depthConj f2
      | f -> 1

    let rec createProjection (psi, depth, a, pattern) = match a with
      | (T.And (f1, f2) as f) ->
          createProjection
            ( I.Decl (psi, T.PDec (None, f1, None, None)),
              depth + 1,
              T.forSub f2 (T.Shift 1),
              T.PairPrg (T.Var (depth + 2), pattern) )
      | f -> (
          let psi' = I.Decl (psi, T.PDec (None, f, None, None)) in
          let depth' = depth + 1 in
          function
          | k ->
              let (T.PDec (_, f', _, _)) = T.ctxDec psi' k in
              ( T.Case
                  (T.Cases
                     [ (psi', T.Dot (T.Prg pattern, T.Shift depth'), T.Var k) ]),
                f' ))

    let rec installProjection (a, n, f, proj) = match a with
      | [] -> []
      | cid :: cids ->
          let p', f' = proj n in
          let p = T.Lam (T.PDec (None, f, None, None), p') in
          let f'' = T.All ((T.PDec (None, f, None, None), T.Explicit), f') in
          let name = I.conDecName (I.sgnLookup cid) in
          ignore (TomegaTypeCheck.checkPrg I.Null (p, f''));
          let lemma = T.lemmaAdd (T.ValDec ("#" ^ name, p, f'')) in
          lemma :: installProjection (cids, n - 1, f, proj)

    let rec installSelection (a, b, c, main) = match a, b, c with
      | cid :: [], lemma :: [], f1 ->
          let p = T.Redex (T.Const lemma, T.AppPrg (T.Const main, T.Nil)) in
          let name = I.conDecName (I.sgnLookup cid) in
          ignore (TomegaTypeCheck.checkPrg I.Null (p, f1));
          let lemma' = T.lemmaAdd (T.ValDec (name, p, f1)) in
          [ lemma' ]
      | cid :: cids, lemma :: lemmas, T.And (f1, f2) ->
          let p = T.Redex (T.Const lemma, T.AppPrg (T.Const main, T.Nil)) in
          let name = I.conDecName (I.sgnLookup cid) in
          ignore (TomegaTypeCheck.checkPrg I.Null (p, f1));
          let lemma' = T.lemmaAdd (T.ValDec (name, p, f1)) in
          lemma' :: installSelection (cids, lemmas, f2, main)

    let installPrg = function
      | cid :: [] ->
          let f = convertFor [ cid ] in
          let p = convertPrg ([ cid ], None) in
          let name = I.conDecName (I.sgnLookup cid) in
          ignore (TomegaTypeCheck.checkPrg I.Null (p, f));
          ignore (Display.chatter_s 4 "[Redundancy Checker (factoring) ...");
          let factP = Redundant.convert p in
          ignore (Display.chatter_s 4 "done]\n");
          let lemma = T.lemmaAdd (T.ValDec (name, factP, f)) in
          (lemma, [], [])
      | cids ->
          let f = convertFor cids in
          ignore (TomegaTypeCheck.checkFor I.Null f);
          let proj = createProjection (I.Null, 0, f, T.Var 1) in
          let projs = installProjection (cids, depthConj f, f, proj) in
          let p = convertPrg (cids, Some projs) in
          let s = name cids in
          ignore (TomegaTypeCheck.checkPrg I.Null (p, f));
          ignore (Display.chatter_s 4 "[Redundancy Checker (factoring) ...");
          let factP = Redundant.convert p in
          ignore (Display.chatter_s 4 "done]\n");
          let lemma = T.lemmaAdd (T.ValDec (s, factP, f)) in
          let sels = installSelection (cids, projs, f, lemma) in
          (lemma, projs, sels)

    let rec mkResult = function
      | 0 -> T.Unit
      | n -> T.PairExp (I.Root (I.BVar n, I.Nil), mkResult (n - 1))

    let convertGoal g v =
      let a = I.targetFam v in
      let w = WorldSyn.lookup a in
      let w', wmap = transformWorlds ([ a ], w) in
      let (Some (_, (p', q'))) =
        traversePos ([], wmap, None)
          ( (I.Null, g, I.Null),
            v,
            Some
              ( I.Shift (I.ctxLength g),
                ( (function p -> (I.Null, T.id, p)),
                  mkResult (I.ctxLength g) ) ) )
      in
      let _, _, p'' = p' q' in
      p''
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
  let convertPrg l = convertPrg (l, None)
  let installFor = installFor
  let installPrg = installPrg
  let traverse = traverse
  let convertGoal = convertGoal
end
(* functor FunSyn *)

(* # 1 "src/tomega/Converter.sml.ml" *)
