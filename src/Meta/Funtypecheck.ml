open! Intsyn.Lambda_
open! Print.Print_
open! Subordinate
open! Typecheck.Typecheck_

(* # 1 "src/meta/Funtypecheck.sig.ml" *)
open Funprint
open Funsyn
open Statesyn

(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)
include FUNTYPECHECK
(* Signature FUNTYPECHECK *)

(* # 1 "src/meta/Funtypecheck.fun.ml" *)
open! Basis

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module FunTypeCheck (FunTypeCheck__0 : sig
  (* Type checking for functional proof term calculus *)
  (* Author: Carsten Schuermann *)
  (*! structure FunSyn' : FUNSYN !*)
  module StateSyn' : STATESYN.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = FunSyn'.IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = FunSyn'.IntSyn !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = FunSyn'.IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = FunSyn'.IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = FunSyn'.IntSyn !*)
  module Subordinate : Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = FunSyn'.IntSyn !*)
  module Weaken : WEAKEN.WEAKEN

  (*! sharing Weaken.IntSyn = FunSyn'.IntSyn   !*)
  module FunPrint : FUNPRINT.FUNPRINT
end) : FUNTYPECHECK.FUNTYPECHECK = struct
  (*! structure FunSyn = FunSyn' !*)
  open FunTypeCheck__0
  module StateSyn = StateSyn'

  exception Error = Error

  open! struct
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn

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

    let rec extend (g, a) = match a with
      | [] -> g
      | d :: l -> extend (I.Decl (g, d), l)

    let validBlock (psi, k, (l, g)) =
      let rec skipBlock (a, k) = match a with
        | I.Null -> k
        | I.Decl (g', _) -> skipBlock (g', k - 1)
      in
      let rec validBlock' = function
        | I.Decl (psi, F.Block (F.CtxBlock (l', g'))), 0 ->
            begin if l' = l && conv (g, I.id) (g', I.id) then ()
            else raise (Error "Typecheck Error: Not a valid block")
            end
        | I.Decl (psi, F.Prim _), 0 ->
            raise (Error "Typecheck Error: Not a valid block")
        | I.Null, k -> raise (Error "Typecheck Error: Not a valid block")
        | I.Decl (psi, F.Block (F.CtxBlock (l', g'))), k ->
            validBlock' (psi, skipBlock (g', k))
        | I.Decl (psi, F.Prim d), k -> validBlock' (psi, k - 1)
      in
      validBlock' (psi, k)

    let raiseSub (g, psi') =
      let n = I.ctxLength g in
      let m = I.ctxLength psi' in
      let rec args (n', a, s) = match n' with
        | 0 -> s
        | n' ->
            let (I.Dec (_, v)) = I.ctxDec g n' in
            begin if Subordinate.belowEq (I.targetFam v) a then
              args (n' - 1, a, I.App (I.Root (I.BVar n', I.Nil), s))
            else args (n' - 1, a, s)
            end
      in
      let term m' =
        let (I.Dec (_, v)) = I.ctxDec psi' m' in
        I.Exp (I.Root (I.BVar (n + m'), args (n, I.targetFam v, I.Nil)))
      in
      let rec raiseSub'' (m', s) = match m' with
        | 0 -> s
        | m' -> raiseSub'' (m' - 1, I.Dot (term m', s))
      in
      let rec raiseSub' (n', s) = match n' with
        | 0 -> raiseSub'' (m, s)
        | n' -> raiseSub' (n' - 1, I.Dot (I.Idx n', s))
      in
      raiseSub' (n, I.Shift (n + m))

    let raiseType (F.CtxBlock (l, g)) psi' =
      let rec raiseType'' (b, vn, a) = match b with
        | I.Null -> vn
        | I.Decl (g', (I.Dec (_, v') as d)) ->
            begin if Subordinate.belowEq (I.targetFam v') a then
              raiseType'' (g', Abstract.piDepend d I.Maybe vn, a)
            else raiseType'' (g', Weaken.strengthenExp vn I.shift, a)
            end
      in
      let rec raiseType' (psi1, b) = match b with
        | [] -> []
        | F.Prim (I.Dec (x, v) as d) :: psi1' ->
            let s = raiseSub (g, psi1) in
            let vn = Whnf.normalize (v, s) in
            let a = I.targetFam vn in
            let d' = I.Dec (x, raiseType'' (g, vn, a)) in
            F.Prim d' :: raiseType' (I.Decl (psi1, d), psi1')
      in
      raiseType' (I.Null, psi')

    let rec raiseM (b, a) = match a with
      | [] -> []
      | F.MDec (xx, f) :: l ->
          F.MDec (xx, F.All (F.Block b, f)) :: raiseM (b, l)

    let rec psub (k, a, s) = match a with
      | I.Null -> s
      | I.Decl (g, _) -> psub (k - 1, g, I.Dot (I.Idx k, s))

    let rec deltaSub (a, s) = match a with
      | I.Null -> I.Null
      | I.Decl (delta, dd) -> I.Decl (deltaSub (delta, s), F.mdecSub dd s)

    let shift delta = deltaSub (delta, I.shift)

    let rec shifts (a, delta) = match a with
      | I.Null -> delta
      | I.Decl (g, _) -> shifts (g, shift delta)

    let shiftBlock (F.CtxBlock (_, g), delta) = shifts (g, delta)

    let rec shiftSub (a, s) = match a with
      | I.Null -> s
      | I.Decl (g, _) -> shiftSub (g, I.comp I.shift s)

    let shiftSubBlock (F.CtxBlock (_, g), s) = shiftSub (g, s)

    let rec check = function
      | psi, delta, F.Unit, (F.True, _) -> ()
      | psi, delta, F.Rec (dd, p), f -> check (psi, I.Decl (delta, dd), p, f)
      | ( psi,
          delta,
          F.Lam ((F.Prim (I.Dec (_, v)) as ld), p),
          (F.All (F.Prim (I.Dec (_, v')), f'), s') ) ->
          begin if Conv.conv (v, I.id) (v', s') then
            check (I.Decl (psi, ld), shift delta, p, (f', I.dot1 s'))
          else raise (Error "Typecheck Error: Primitive Abstraction")
          end
      | ( psi,
          delta,
          F.Lam ((F.Block (F.CtxBlock (l, g) as b) as ld), p),
          (F.All (F.Block (F.CtxBlock (l', g')), f'), s') ) ->
          begin if l = l' && conv (g, I.id) (g', s') then
            check
              ( I.Decl (psi, ld),
                shiftBlock (b, delta),
                p,
                (f', F.dot1n g s') )
          else raise (Error "Typecheck Error: Block Abstraction")
          end
      | psi, delta, F.Inx (m, p), (F.Ex (I.Dec (_, v'), f'), s') -> begin
          TypeCheck.typeCheck (F.makectx psi) (m, I.EClo (v', s'));
          check (psi, delta, p, (f', I.Dot (I.Exp m, s')))
        end
      | psi, delta, F.Case (F.Opts o), (f', s') ->
          checkOpts (psi, delta, o, (f', s'))
      | psi, delta, F.Pair (p1, p2), (F.And (f1', f2'), s') -> begin
          check (psi, delta, p1, (f1', s'));
          check (psi, delta, p2, (f2', s'))
        end
      | psi, delta, F.Let (ds, p), (f', s') ->
          let psi', delta', s'' = assume (psi, delta, ds) in
          check
            ( extend (psi, psi'),
              extend (delta, delta'),
              p,
              (f', I.comp s' s'') )
      | _ -> raise (Error "Typecheck Error: Term not well-typed")

    and infer (delta, kk) = (I.ctxLookup delta kk, I.id)

    and assume (psi, delta, empty) = match empty with
      | empty -> ([], [], I.id)
      | F.Split (kk, ds) ->
          begin match infer (delta, kk) with
          | F.MDec (name, F.Ex (d, f)), s ->
              let ld = F.Prim (I.decSub d s) in
              let dd = F.MDec (name, F.forSub f (I.dot1 s)) in
              let psi', delta', s' =
                assume (I.Decl (psi, ld), I.Decl (shift delta, dd), ds)
              in
              (ld :: psi', F.mdecSub dd s' :: delta', I.comp I.shift s')
          | _ -> raise (Error "Typecheck Error: Declaration")
          end
      | F.New (b, ds) ->
          ignore (TypeCheck.typeCheck
              (F.makectx (I.Decl (psi, F.Block b))) (I.Uni I.Type, I.Uni I.Kind));
          let psi', delta', s' =
            assume (I.Decl (psi, F.Block b), shiftBlock (b, delta), ds)
          in
          (raiseType b psi', raiseM (b, delta'), s')
      | F.App ((kk, u), ds) ->
          begin match infer (delta, kk) with
          | F.MDec (name, F.All (F.Prim (I.Dec (_, v)), f)), s ->
              ignore (try TypeCheck.typeCheck (F.makectx psi) (u, I.EClo (v, s))
                with TypeCheck.Error msg ->
                  raise
                    (Error
                       ((((((msg ^ " ") ^ Print.expToString (F.makectx psi) u)
                          ^ " has type ")
                         ^ Print.expToString
                             (F.makectx psi) (TypeCheck.infer' (F.makectx psi) u))
                        ^ " expected ")
                       ^ Print.expToString (F.makectx psi) (I.EClo (v, s)))));
              let dd = F.MDec (name, F.forSub f (I.Dot (I.Exp u, s))) in
              let psi', delta', s' = assume (psi, I.Decl (delta, dd), ds) in
              (psi', F.mdecSub dd s' :: delta', s')
          | F.MDec (name, f), s ->
              raise
                (Error
                   ("Typecheck Error: Declaration App"
                   ^ FunPrint.forToString I.Null f [ "x" ]))
          end
      | F.PApp ((kk, k), ds) ->
          begin match infer (delta, kk) with
          | F.MDec (name, F.All (F.Block (F.CtxBlock (l, g)), f)), s ->
              ignore (validBlock (psi, k, (l, g)));
              let dd = F.MDec (name, F.forSub f (psub (k, g, s))) in
              let psi', delta', s' = assume (psi, I.Decl (delta, dd), ds) in
              (psi', F.mdecSub dd s' :: delta', s')
          | _ -> raise (Error "Typecheck Error: Declaration PApp")
          end
      | F.Left (kk, ds) ->
          begin match infer (delta, kk) with
          | F.MDec (name, F.And (f1, f2)), s ->
              let dd = F.MDec (name, F.forSub f1 s) in
              let psi', delta', s' = assume (psi, I.Decl (delta, dd), ds) in
              (psi', F.mdecSub dd s' :: delta', s')
          | _ -> raise (Error "Typecheck Error: Declaration Left")
          end
      | F.Right (kk, ds) ->
          begin match infer (delta, kk) with
          | F.MDec (name, F.And (f1, f2)), s ->
              let dd = F.MDec (name, F.forSub f2 s) in
              let psi', delta', s' = assume (psi, I.Decl (delta, dd), ds) in
              (psi', F.mdecSub dd s' :: delta', s')
          | _ -> raise (Error "Typecheck Error: Declaration Left")
          end
      | F.Lemma (cc, ds) ->
          let (F.LemmaDec (names, _, f)) = F.lemmaLookup cc in
          let name = foldr (fun (x__op, y__op) -> x__op ^ y__op) "" names in
          let dd = F.MDec (Some name, f) in
          let psi', delta', s' = assume (psi, I.Decl (delta, dd), ds) in
          (psi', F.mdecSub dd s' :: delta', s')

    and checkSub a1 b1 c1 = match a1, b1, c1 with
      | I.Null, I.Shift 0, I.Null -> ()
      | I.Decl (psi, F.Prim d), I.Shift k, I.Null ->
          begin if k > 0 then checkSub psi (I.Shift (k - 1)) I.Null
          else raise (Error "Substitution not well-typed")
          end
      | I.Decl (psi, F.Block (F.CtxBlock (_, g_))), I.Shift k, I.Null ->
          let g = I.ctxLength g_ in
          begin if k >= g then checkSub psi (I.Shift (k - g)) I.Null
          else raise (Error "Substitution not well-typed")
          end
      | psi', I.Shift k, psi ->
          checkSub psi' (I.Dot (I.Idx (k + 1), I.Shift (k + 1))) psi
      | psi', I.Dot (I.Idx k, s'), I.Decl (psi, F.Prim (I.Dec (_, v2))) ->
          let g' = F.makectx psi' in
          let (I.Dec (_, v1)) = I.ctxDec g' k in
          begin if Conv.conv (v1, I.id) (v2, s') then
            checkSub psi' s' psi
          else
            raise
              (Error
                 ((("Substitution not well-typed \n  found: "
                   ^ Print.expToString g' v1)
                  ^ "\n  expected: ")
                 ^ Print.expToString g' (I.EClo (v2, s'))))
          end
      | psi', I.Dot (I.Exp u, s'), I.Decl (psi, F.Prim (I.Dec (_, v2))) ->
          let g' = F.makectx psi' in
          ignore (TypeCheck.typeCheck g' (u, I.EClo (v2, s')));
          checkSub psi' s' psi
      | ( psi',
          (I.Dot (I.Idx k, _) as s),
          I.Decl (psi, F.Block (F.CtxBlock (l1, g))) ) ->
          let F.Block (F.CtxBlock (l2, g')), w = F.lfctxLFDec psi' k in
          let rec checkSub' (a, b, c, m) = match a, b, c with
            | (I.Null, w1), s1, I.Null -> s1
            | (I.Decl (g', I.Dec (_, v')), w1), I.Dot (I.Idx k', s1), I.Decl (g, I.Dec (_, v)) ->
                begin if k' = m then
                  begin if Conv.conv (v', w1) (v, s1) then
                    checkSub' ((g', I.comp w1 I.shift), s1, g, m + 1)
                  else raise (Error "ContextBlock assignment not well-typed")
                  end
                else raise (Error "ContextBlock assignment out of order")
                end
          in
          checkSub psi' (checkSub' ((g', w), s, g, k)) psi

    and checkOpts (psi, delta, a, b) = match a, b with
      | [], _ -> ()
      | (psi', t, p) :: o, (f', s') -> begin
          checkSub psi' t psi;
          begin
            check (psi', deltaSub (delta, t), p, (f', I.comp s' t));
            checkOpts (psi, delta, o, (f', s'))
          end
        end

    let checkRec (p, t) = check (I.Null, I.Null, p, (t, I.id))

    let rec isFor a1 b1 = match a1, b1 with
      | g, F.All (F.Prim d, f) -> (
          try
            begin
              TypeCheck.checkDec g (d, I.id);
              isFor (I.Decl (g, d)) f
            end
          with TypeCheck.Error msg -> raise (Error msg))
      | g, F.All (F.Block (F.CtxBlock (_, g1)), f) ->
          isForBlock (g, F.ctxToList g1, f)
      | g, F.Ex (d, f) -> (
          try
            begin
              TypeCheck.checkDec g (d, I.id);
              isFor (I.Decl (g, d)) f
            end
          with TypeCheck.Error msg -> raise (Error msg))
      | g, True -> ()
      | g, F.And (f1, f2) -> begin
          isFor g f1;
          isFor g f2
        end

    and isForBlock (g, a, f) = match a with
      | [] -> isFor g f
      | d :: g1 -> isForBlock (I.Decl (g, d), g1, f)

    let rec checkTags' = function
      | v, F.Ex _ -> ()
      | I.Pi (_, v), F.All (_, f) -> checkTags' (v, f)
      | _ -> raise Domain

    let rec checkTags = function
      | I.Null, I.Null -> ()
      | I.Decl (g, I.Dec (_, v)), I.Decl (b, t) -> begin
          checkTags (g, b);
          begin match t with S.Lemma _ -> () | _ -> ()
          end
        end

    let isState (S.State (n, (g, b), (ih, oh), d, o, h, f)) =
      begin
        TypeCheck.typeCheckCtx g;
        begin
          checkTags (g, b);
          begin
            begin if not (Abstract.closedCtx g) then
              raise (Error "State context not closed!")
            else ()
            end;
            begin
              ignore (map (function n', f' -> isFor g f') h);
              isFor g f
            end
          end
        end
      end
  end

  (* conv ((G, s), (G', s')) = B

       Invariant:
       B iff G [s]  == G' [s']
       Might migrate in to conv module  --cs
    *)
  (* extend (G, L) = G'

       Invariant:
       If   G : 'a ctx
       and  L : 'a list
       then G' = G, L : 'a ctx
    *)
  (* validBlock (Psi, k, (l : G)) = ()

       Invariant:
       If   |- Psi ctx
       and  |- k is a debruijn index (for LF context)
       and  |- l label
       and  |- G LFctx
       then validBlock terminates with ()
       iff  Psi = Psi1, l': (x1:A1 .. xn:An), Psi2
       and  l = l'
       and  Psi(k) = x1
       and  G == x1:A1 .. xn:An
    *)
  (* raiseSub (l:G, Psi') = s'

       Invariant:
       If   |- Psi ctx
       and  Psi |- l:G ctx
       and  Psi, l:G |- Psi' ctx
       then Psi, {G} Psi', l:G|- s' : Psi, l:G, Psi'
    *)
  (* raiseType (l:G, L) = L'

       Invariant:
       L contains no parameter block declarations
       Each x:A in L is mapped xto  x:{G}A in L'
       L' preserves the order of L
    *)
  (* no case of F.Block by invariant *)
  (* raiseM (B, L) = L'

       Invariant
       Each xx in F in L is mapped to xx in PI B. F in L'
       L' preserves the order of L
    *)
  (* psub (k, Phi, s) = s'

       Invariant:
       If   |- Phi ctx
       and  |- Psi ctx
       and  Psi = Psi1, l': (x1:A1 .. xn:An), Psi2
       and  Psi (k) = x1
       and  | Phi | = n
       and  s = k-i ... k. id   for i <=n
       then s' = k-n . ... k . id
    *)
  (* check (Psi, Delta, P, (F, s)) = ()

       Invariant:
       If   Psi'' |- F formula
       and  Psi |- s : Psi''
       and  Psi |- Delta mctx
        returns () if there exists a F',
              s.t. Psi, Delta |- P  : F'
              and  Psi |- F' = F[s] formula
       otherwise Error is raised
    *)
  (* assume (Psi, Delta, Ds) = (Psi', Delta', s')

       Invariant:
       If   |- Psi context
       and  Psi |- Delta assumptions
       and  Psi, Delta |- Decs declarations
       then |- Psi, Psi' context
       and  Psi, Psi' |- Delta, Delta' assumptions
       and  Psi, Psi' |- s' = ^|Psi'| : Psi
    *)
  (* check B valid context block       <-------------- omission *)
  (* checkSub (Psi1, s, Psi2) = ()

       Invariant:
       The function terminates
       iff  Psi1 |- s : Psi2
    *)
  (* check that l1 = l2     <----------------------- omission *)
  (* checkSub' ((G', w), s, G, m) = ()
          *)
  (* checkOpts (Psi, Delta, (O, s) *)
  (* [Psi' strict in  t] <------------------------- omission*)
  (* isState (S) = ()

       Invariant:

       Side effect:
       If it doesn't hold that |- S state, then exception Error is raised

       Remark: Function is only partially implemented
    *)
  (* ;          TextIO.print (""Checked: "" ^ (FunPrint.Formatter.makestring_fmt (FunPrint.formatForBare (G, F'))) ^ ""\n"") *)
  (* n' is not checked for consistency   --cs *)
  let isFor = isFor
  let check = checkRec
  let checkSub = checkSub
  let isState = isState
end
(*! sharing FunPrint.FunSyn = FunSyn' !*)
(* Signature FUNTYPECHECK *)

(* # 1 "src/meta/Funtypecheck.sml.ml" *)
