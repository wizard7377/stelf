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

(* # 1 "src/meta/Funtypecheck.sig.ml" *)
open! Basis
open Funprint
open Funsyn
open Statesyn

(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)
include FUNTYPECHECK
(* Signature FUNTYPECHECK *)

(* # 1 "src/meta/Funtypecheck.fun.ml" *)
open! Weaken
open! Print
open! Abstract
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

    let conv gs_ gs' =
      let exception Conv in
      let rec conv a1 b1 = match a1, b1 with
        | (I.Null, s), (I.Null, s') -> (s, s')
        | (I.Decl (g_, I.Dec (_, v_)), s), (I.Decl (g'_, I.Dec (_, v'_)), s') ->
            let s1, s1' = conv (g_, s) (g'_, s') in
            let ((s2, s2') as ps) = (I.dot1 s1, I.dot1 s1') in
            begin if Conv.conv (v_, s1) (v'_, s1') then ps else raise Conv
            end
        | _ -> raise Conv
      in
      try
        begin
          ignore (conv gs_ gs');
          true
        end
      with Conv -> false

    let rec extend (g_, a) = match a with
      | [] -> g_
      | d_ :: l_ -> extend (I.Decl (g_, d_), l_)

    let validBlock (psi, k, (l, g_)) =
      let rec skipBlock (a, k) = match a with
        | I.Null -> k
        | I.Decl (g'_, _) -> skipBlock (g'_, k - 1)
      in
      let rec validBlock' = function
        | I.Decl (psi, F.Block (F.CtxBlock (l', g'_))), 0 ->
            begin if l' = l && conv (g_, I.id) (g'_, I.id) then ()
            else raise (Error "Typecheck Error: Not a valid block")
            end
        | I.Decl (psi, F.Prim _), 0 ->
            raise (Error "Typecheck Error: Not a valid block")
        | I.Null, k -> raise (Error "Typecheck Error: Not a valid block")
        | I.Decl (psi, F.Block (F.CtxBlock (l', g'_))), k ->
            validBlock' (psi, skipBlock (g'_, k))
        | I.Decl (psi, F.Prim d_), k -> validBlock' (psi, k - 1)
      in
      validBlock' (psi, k)

    let raiseSub (g_, psi') =
      let n = I.ctxLength g_ in
      let m = I.ctxLength psi' in
      let rec args (n', a, s_) = match n' with
        | 0 -> s_
        | n' ->
            let (I.Dec (_, v_)) = I.ctxDec g_ n' in
            begin if Subordinate.belowEq (I.targetFam v_) a then
              args (n' - 1, a, I.App (I.Root (I.BVar n', I.Nil), s_))
            else args (n' - 1, a, s_)
            end
      in
      let term m' =
        let (I.Dec (_, v_)) = I.ctxDec psi' m' in
        I.Exp (I.Root (I.BVar (n + m'), args (n, I.targetFam v_, I.Nil)))
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

    let raiseType (F.CtxBlock (l, g_)) psi' =
      let rec raiseType'' (b, vn, a) = match b with
        | I.Null -> vn
        | I.Decl (g'_, (I.Dec (_, v'_) as d_)) ->
            begin if Subordinate.belowEq (I.targetFam v'_) a then
              raiseType'' (g'_, Abstract.piDepend d_ I.Maybe vn, a)
            else raiseType'' (g'_, Weaken.strengthenExp vn I.shift, a)
            end
      in
      let rec raiseType' (psi1, b) = match b with
        | [] -> []
        | F.Prim (I.Dec (x, v_) as d_) :: psi1' ->
            let s = raiseSub (g_, psi1) in
            let vn = Whnf.normalize (v_, s) in
            let a = I.targetFam vn in
            let d'_ = I.Dec (x, raiseType'' (g_, vn, a)) in
            F.Prim d'_ :: raiseType' (I.Decl (psi1, d_), psi1')
      in
      raiseType' (I.Null, psi')

    let rec raiseM (b_, a) = match a with
      | [] -> []
      | F.MDec (xx, f_) :: l_ ->
          F.MDec (xx, F.All (F.Block b_, f_)) :: raiseM (b_, l_)

    let rec psub (k, a, s) = match a with
      | I.Null -> s
      | I.Decl (g_, _) -> psub (k - 1, g_, I.Dot (I.Idx k, s))

    let rec deltaSub (a, s) = match a with
      | I.Null -> I.Null
      | I.Decl (delta, dd) -> I.Decl (deltaSub (delta, s), F.mdecSub dd s)

    let shift delta = deltaSub (delta, I.shift)

    let rec shifts (a, delta) = match a with
      | I.Null -> delta
      | I.Decl (g_, _) -> shifts (g_, shift delta)

    let shiftBlock (F.CtxBlock (_, g_), delta) = shifts (g_, delta)

    let rec shiftSub (a, s) = match a with
      | I.Null -> s
      | I.Decl (g_, _) -> shiftSub (g_, I.comp I.shift s)

    let shiftSubBlock (F.CtxBlock (_, g_), s) = shiftSub (g_, s)

    let rec check = function
      | psi, delta, F.Unit, (F.True, _) -> ()
      | psi, delta, F.Rec (dd, p_), f_ -> check (psi, I.Decl (delta, dd), p_, f_)
      | ( psi,
          delta,
          F.Lam ((F.Prim (I.Dec (_, v_)) as ld), p_),
          (F.All (F.Prim (I.Dec (_, v'_)), f'_), s') ) ->
          begin if Conv.conv (v_, I.id) (v'_, s') then
            check (I.Decl (psi, ld), shift delta, p_, (f'_, I.dot1 s'))
          else raise (Error "Typecheck Error: Primitive Abstraction")
          end
      | ( psi,
          delta,
          F.Lam ((F.Block (F.CtxBlock (l, g_) as b_) as ld), p_),
          (F.All (F.Block (F.CtxBlock (l', g'_)), f'_), s') ) ->
          begin if l = l' && conv (g_, I.id) (g'_, s') then
            check
              ( I.Decl (psi, ld),
                shiftBlock (b_, delta),
                p_,
                (f'_, F.dot1n g_ s') )
          else raise (Error "Typecheck Error: Block Abstraction")
          end
      | psi, delta, F.Inx (m_, p_), (F.Ex (I.Dec (_, v'_), f'_), s') -> begin
          TypeCheck.typeCheck (F.makectx psi) (m_, I.EClo (v'_, s'));
          check (psi, delta, p_, (f'_, I.Dot (I.Exp m_, s')))
        end
      | psi, delta, F.Case (F.Opts o_), (f'_, s') ->
          checkOpts (psi, delta, o_, (f'_, s'))
      | psi, delta, F.Pair (p1_, p2_), (F.And (f1', f2'), s') -> begin
          check (psi, delta, p1_, (f1', s'));
          check (psi, delta, p2_, (f2', s'))
        end
      | psi, delta, F.Let (ds_, p_), (f'_, s') ->
          let psi', delta', s'' = assume (psi, delta, ds_) in
          check
            ( extend (psi, psi'),
              extend (delta, delta'),
              p_,
              (f'_, I.comp s' s'') )
      | _ -> raise (Error "Typecheck Error: Term not well-typed")

    and infer (delta, kk) = (I.ctxLookup delta kk, I.id)

    and assume (psi, delta, empty_) = match empty_ with
      | empty_ -> ([], [], I.id)
      | F.Split (kk, ds_) ->
          begin match infer (delta, kk) with
          | F.MDec (name, F.Ex (d_, f_)), s ->
              let ld = F.Prim (I.decSub d_ s) in
              let dd = F.MDec (name, F.forSub f_ (I.dot1 s)) in
              let psi', delta', s' =
                assume (I.Decl (psi, ld), I.Decl (shift delta, dd), ds_)
              in
              (ld :: psi', F.mdecSub dd s' :: delta', I.comp I.shift s')
          | _ -> raise (Error "Typecheck Error: Declaration")
          end
      | F.New (b_, ds_) ->
          ignore (TypeCheck.typeCheck
              (F.makectx (I.Decl (psi, F.Block b_))) (I.Uni I.Type, I.Uni I.Kind));
          let psi', delta', s' =
            assume (I.Decl (psi, F.Block b_), shiftBlock (b_, delta), ds_)
          in
          (raiseType b_ psi', raiseM (b_, delta'), s')
      | F.App ((kk, u_), ds_) ->
          begin match infer (delta, kk) with
          | F.MDec (name, F.All (F.Prim (I.Dec (_, v_)), f_)), s ->
              ignore (try TypeCheck.typeCheck (F.makectx psi) (u_, I.EClo (v_, s))
                with TypeCheck.Error msg ->
                  raise
                    (Error
                       ((((((msg ^ " ") ^ Print.expToString (F.makectx psi) u_)
                          ^ " has type ")
                         ^ Print.expToString
                             (F.makectx psi) (TypeCheck.infer' (F.makectx psi) u_))
                        ^ " expected ")
                       ^ Print.expToString (F.makectx psi) (I.EClo (v_, s)))));
              let dd = F.MDec (name, F.forSub f_ (I.Dot (I.Exp u_, s))) in
              let psi', delta', s' = assume (psi, I.Decl (delta, dd), ds_) in
              (psi', F.mdecSub dd s' :: delta', s')
          | F.MDec (name, f_), s ->
              raise
                (Error
                   ("Typecheck Error: Declaration App"
                   ^ FunPrint.forToString I.Null f_ [ "x" ]))
          end
      | F.PApp ((kk, k), ds_) ->
          begin match infer (delta, kk) with
          | F.MDec (name, F.All (F.Block (F.CtxBlock (l, g_)), f_)), s ->
              ignore (validBlock (psi, k, (l, g_)));
              let dd = F.MDec (name, F.forSub f_ (psub (k, g_, s))) in
              let psi', delta', s' = assume (psi, I.Decl (delta, dd), ds_) in
              (psi', F.mdecSub dd s' :: delta', s')
          | _ -> raise (Error "Typecheck Error: Declaration PApp")
          end
      | F.Left (kk, ds_) ->
          begin match infer (delta, kk) with
          | F.MDec (name, F.And (f1_, f2_)), s ->
              let dd = F.MDec (name, F.forSub f1_ s) in
              let psi', delta', s' = assume (psi, I.Decl (delta, dd), ds_) in
              (psi', F.mdecSub dd s' :: delta', s')
          | _ -> raise (Error "Typecheck Error: Declaration Left")
          end
      | F.Right (kk, ds_) ->
          begin match infer (delta, kk) with
          | F.MDec (name, F.And (f1_, f2_)), s ->
              let dd = F.MDec (name, F.forSub f2_ s) in
              let psi', delta', s' = assume (psi, I.Decl (delta, dd), ds_) in
              (psi', F.mdecSub dd s' :: delta', s')
          | _ -> raise (Error "Typecheck Error: Declaration Left")
          end
      | F.Lemma (cc, ds_) ->
          let (F.LemmaDec (names, _, f_)) = F.lemmaLookup cc in
          let name = foldr (fun (x__op, y__op) -> x__op ^ y__op) "" names in
          let dd = F.MDec (Some name, f_) in
          let psi', delta', s' = assume (psi, I.Decl (delta, dd), ds_) in
          (psi', F.mdecSub dd s' :: delta', s')

    and checkSub a1 b1 c1 = match a1, b1, c1 with
      | I.Null, I.Shift 0, I.Null -> ()
      | I.Decl (psi, F.Prim d_), I.Shift k, I.Null ->
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
      | psi', I.Dot (I.Idx k, s'), I.Decl (psi, F.Prim (I.Dec (_, v2_))) ->
          let g'_ = F.makectx psi' in
          let (I.Dec (_, v1_)) = I.ctxDec g'_ k in
          begin if Conv.conv (v1_, I.id) (v2_, s') then
            checkSub psi' s' psi
          else
            raise
              (Error
                 ((("Substitution not well-typed \n  found: "
                   ^ Print.expToString g'_ v1_)
                  ^ "\n  expected: ")
                 ^ Print.expToString g'_ (I.EClo (v2_, s'))))
          end
      | psi', I.Dot (I.Exp u_, s'), I.Decl (psi, F.Prim (I.Dec (_, v2_))) ->
          let g'_ = F.makectx psi' in
          ignore (TypeCheck.typeCheck g'_ (u_, I.EClo (v2_, s')));
          checkSub psi' s' psi
      | ( psi',
          (I.Dot (I.Idx k, _) as s),
          I.Decl (psi, F.Block (F.CtxBlock (l1, g_))) ) ->
          let F.Block (F.CtxBlock (l2, g'_)), w = F.lfctxLFDec psi' k in
          let rec checkSub' (a, b, c, m) = match a, b, c with
            | (I.Null, w1), s1, I.Null -> s1
            | (I.Decl (g'_, I.Dec (_, v'_)), w1), I.Dot (I.Idx k', s1), I.Decl (g_, I.Dec (_, v_)) ->
                begin if k' = m then
                  begin if Conv.conv (v'_, w1) (v_, s1) then
                    checkSub' ((g'_, I.comp w1 I.shift), s1, g_, m + 1)
                  else raise (Error "ContextBlock assignment not well-typed")
                  end
                else raise (Error "ContextBlock assignment out of order")
                end
          in
          checkSub psi' (checkSub' ((g'_, w), s, g_, k)) psi

    and checkOpts (psi, delta, a, b) = match a, b with
      | [], _ -> ()
      | (psi', t, p_) :: o_, (f'_, s') -> begin
          checkSub psi' t psi;
          begin
            check (psi', deltaSub (delta, t), p_, (f'_, I.comp s' t));
            checkOpts (psi, delta, o_, (f'_, s'))
          end
        end

    let checkRec (p_, t_) = check (I.Null, I.Null, p_, (t_, I.id))

    let rec isFor a1 b1 = match a1, b1 with
      | g_, F.All (F.Prim d_, f_) -> (
          try
            begin
              TypeCheck.checkDec g_ (d_, I.id);
              isFor (I.Decl (g_, d_)) f_
            end
          with TypeCheck.Error msg -> raise (Error msg))
      | g_, F.All (F.Block (F.CtxBlock (_, g1_)), f_) ->
          isForBlock (g_, F.ctxToList g1_, f_)
      | g_, F.Ex (d_, f_) -> (
          try
            begin
              TypeCheck.checkDec g_ (d_, I.id);
              isFor (I.Decl (g_, d_)) f_
            end
          with TypeCheck.Error msg -> raise (Error msg))
      | g_, True -> ()
      | g_, F.And (f1_, f2_) -> begin
          isFor g_ f1_;
          isFor g_ f2_
        end

    and isForBlock (g_, a, f_) = match a with
      | [] -> isFor g_ f_
      | d_ :: g1_ -> isForBlock (I.Decl (g_, d_), g1_, f_)

    let rec checkTags' = function
      | v_, F.Ex _ -> ()
      | I.Pi (_, v_), F.All (_, f_) -> checkTags' (v_, f_)
      | _ -> raise Domain

    let rec checkTags = function
      | I.Null, I.Null -> ()
      | I.Decl (g_, I.Dec (_, v_)), I.Decl (b_, t_) -> begin
          checkTags (g_, b_);
          begin match t_ with S.Lemma _ -> () | _ -> ()
          end
        end

    let isState (S.State (n, (g_, b_), (ih_, oh), d, o_, h_, f_)) =
      begin
        TypeCheck.typeCheckCtx g_;
        begin
          checkTags (g_, b_);
          begin
            begin if not (Abstract.closedCtx g_) then
              raise (Error "State context not closed!")
            else ()
            end;
            begin
              ignore (map (function n', f'_ -> isFor g_ f'_) h_);
              isFor g_ f_
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
