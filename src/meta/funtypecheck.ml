(* # 1 "src/meta/funtypecheck.sig.ml" *)
open! Basis
open Funprint
open Funsyn
open Statesyn

(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)
module type FUNTYPECHECK = sig
  (*! structure FunSyn : FUNSYN !*)
  module StateSyn : STATESYN

  exception Error of string

  val isFor : IntSyn.dctx * FunSyn.for_ -> unit
  val check : FunSyn.pro * FunSyn.for_ -> unit
  val checkSub : FunSyn.lfctx * IntSyn.sub * FunSyn.lfctx -> unit
  val isState : StateSyn.state -> unit
end
(* Signature FUNTYPECHECK *)

(* # 1 "src/meta/funtypecheck.fun.ml" *)
open! Weaken
open! Print
open! Abstract
open! Basis

module FunTypeCheck (FunTypeCheck__0 : sig
  (* Type checking for functional proof term calculus *)
  (* Author: Carsten Schuermann *)
  (*! structure FunSyn' : FUNSYN !*)
  module StateSyn' : STATESYN

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
  module Subordinate : SUBORDINATE

  (*! sharing Subordinate.IntSyn = FunSyn'.IntSyn !*)
  module Weaken : WEAKEN

  (*! sharing Weaken.IntSyn = FunSyn'.IntSyn   !*)
  module FunPrint : FUNPRINT
end) : FUNTYPECHECK = struct
  (*! structure FunSyn = FunSyn' !*)
  open FunTypeCheck__0
  module StateSyn = StateSyn'

  exception Error of string

  open! struct
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn

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

    let rec extend = function
      | g_, [] -> g_
      | g_, d_ :: l_ -> extend (I.Decl (g_, d_), l_)

    let rec validBlock (psi_, k, (l, g_)) =
      let rec skipBlock = function
        | I.Null, k -> k
        | I.Decl (g'_, _), k -> skipBlock (g'_, k - 1)
      in
      let rec validBlock' = function
        | I.Decl (psi_, F.Block (F.CtxBlock (l', g'_))), 0 -> begin
            if l' = l && conv ((g_, I.id), (g'_, I.id)) then ()
            else raise (Error "Typecheck Error: Not a valid block")
          end
        | I.Decl (psi_, F.Prim _), 0 ->
            raise (Error "Typecheck Error: Not a valid block")
        | I.Null, k -> raise (Error "Typecheck Error: Not a valid block")
        | I.Decl (psi_, F.Block (F.CtxBlock (l', g'_))), k ->
            validBlock' (psi_, skipBlock (g'_, k))
        | I.Decl (psi_, F.Prim d_), k -> validBlock' (psi_, k - 1)
      in
      validBlock' (psi_, k)

    let rec raiseSub (g_, psi'_) =
      let n = I.ctxLength g_ in
      let m = I.ctxLength psi'_ in
      let rec args = function
        | 0, a, s_ -> s_
        | n', a, s_ ->
            let (I.Dec (_, v_)) = I.ctxDec (g_, n') in
            begin if Subordinate.belowEq (I.targetFam v_, a) then
              args (n' - 1, a, I.App (I.Root (I.BVar n', I.Nil), s_))
            else args (n' - 1, a, s_)
            end
      in
      let rec term m' =
        let (I.Dec (_, v_)) = I.ctxDec (psi'_, m') in
        I.Exp (I.Root (I.BVar (n + m'), args (n, I.targetFam v_, I.Nil)))
      in
      let rec raiseSub'' = function
        | 0, s -> s
        | m', s -> raiseSub'' (m' - 1, I.Dot (term m', s))
      in
      let rec raiseSub' = function
        | 0, s -> raiseSub'' (m, s)
        | n', s -> raiseSub' (n' - 1, I.Dot (I.Idx n', s))
      in
      raiseSub' (n, I.Shift (n + m))

    let rec raiseType (F.CtxBlock (l, g_), psi'_) =
      let rec raiseType'' = function
        | I.Null, vn_, a -> vn_
        | I.Decl (g'_, (I.Dec (_, v'_) as d_)), vn_, a -> begin
            if Subordinate.belowEq (I.targetFam v'_, a) then
              raiseType'' (g'_, Abstract.piDepend ((d_, I.Maybe), vn_), a)
            else raiseType'' (g'_, Weaken.strengthenExp (vn_, I.shift), a)
          end
      in
      let rec raiseType' = function
        | psi1_, [] -> []
        | psi1_, F.Prim (I.Dec (x, v_) as d_) :: psi1'_ ->
            let s = raiseSub (g_, psi1_) in
            let vn_ = Whnf.normalize (v_, s) in
            let a = I.targetFam vn_ in
            let d'_ = I.Dec (x, raiseType'' (g_, vn_, a)) in
            F.Prim d'_ :: raiseType' (I.Decl (psi1_, d_), psi1'_)
      in
      raiseType' (I.Null, psi'_)

    let rec raiseM = function
      | b_, [] -> []
      | b_, F.MDec (xx, f_) :: l_ ->
          F.MDec (xx, F.All (F.Block b_, f_)) :: raiseM (b_, l_)

    let rec psub = function
      | k, I.Null, s -> s
      | k, I.Decl (g_, _), s -> psub (k - 1, g_, I.Dot (I.Idx k, s))

    let rec deltaSub = function
      | I.Null, s -> I.Null
      | I.Decl (delta_, dd_), s ->
          I.Decl (deltaSub (delta_, s), F.mdecSub (dd_, s))

    let rec shift delta_ = deltaSub (delta_, I.shift)

    let rec shifts = function
      | I.Null, delta_ -> delta_
      | I.Decl (g_, _), delta_ -> shifts (g_, shift delta_)

    let rec shiftBlock (F.CtxBlock (_, g_), delta_) = shifts (g_, delta_)

    let rec shiftSub = function
      | I.Null, s -> s
      | I.Decl (g_, _), s -> shiftSub (g_, I.comp (I.shift, s))

    let rec shiftSubBlock (F.CtxBlock (_, g_), s) = shiftSub (g_, s)

    let rec check = function
      | psi_, delta_, F.Unit, (F.True, _) -> ()
      | psi_, delta_, F.Rec (dd_, p_), f_ ->
          check (psi_, I.Decl (delta_, dd_), p_, f_)
      | ( psi_,
          delta_,
          F.Lam ((F.Prim (I.Dec (_, v_)) as ld_), p_),
          (F.All (F.Prim (I.Dec (_, v'_)), f'_), s') ) -> begin
          if Conv.conv ((v_, I.id), (v'_, s')) then
            check (I.Decl (psi_, ld_), shift delta_, p_, (f'_, I.dot1 s'))
          else raise (Error "Typecheck Error: Primitive Abstraction")
        end
      | ( psi_,
          delta_,
          F.Lam ((F.Block (F.CtxBlock (l, g_) as b_) as ld_), p_),
          (F.All (F.Block (F.CtxBlock (l', g'_)), f'_), s') ) -> begin
          if l = l' && conv ((g_, I.id), (g'_, s')) then
            check
              ( I.Decl (psi_, ld_),
                shiftBlock (b_, delta_),
                p_,
                (f'_, F.dot1n (g_, s')) )
          else raise (Error "Typecheck Error: Block Abstraction")
        end
      | psi_, delta_, F.Inx (m_, p_), (F.Ex (I.Dec (_, v'_), f'_), s') -> begin
          TypeCheck.typeCheck (F.makectx psi_, (m_, I.EClo (v'_, s')));
          check (psi_, delta_, p_, (f'_, I.Dot (I.Exp m_, s')))
        end
      | psi_, delta_, F.Case (F.Opts o_), (f'_, s') ->
          checkOpts (psi_, delta_, o_, (f'_, s'))
      | psi_, delta_, F.Pair (p1_, p2_), (F.And (f1'_, f2'_), s') -> begin
          check (psi_, delta_, p1_, (f1'_, s'));
          check (psi_, delta_, p2_, (f2'_, s'))
        end
      | psi_, delta_, F.Let (ds_, p_), (f'_, s') ->
          let psi'_, delta'_, s'' = assume (psi_, delta_, ds_) in
          check
            ( extend (psi_, psi'_),
              extend (delta_, delta'_),
              p_,
              (f'_, I.comp (s', s'')) )
      | _ -> raise (Error "Typecheck Error: Term not well-typed")

    and infer (delta_, kk) = (I.ctxLookup (delta_, kk), I.id)

    and assume = function
      | psi_, delta_, empty_ -> ([], [], I.id)
      | psi_, delta_, F.Split (kk, ds_) -> begin
          match infer (delta_, kk) with
          | F.MDec (name, F.Ex (d_, f_)), s ->
              let ld_ = F.Prim (I.decSub (d_, s)) in
              let dd_ = F.MDec (name, F.forSub (f_, I.dot1 s)) in
              let psi'_, delta'_, s' =
                assume (I.Decl (psi_, ld_), I.Decl (shift delta_, dd_), ds_)
              in
              ( ld_ :: psi'_,
                F.mdecSub (dd_, s') :: delta'_,
                I.comp (I.shift, s') )
          | _ -> raise (Error "Typecheck Error: Declaration")
        end
      | psi_, delta_, F.New (b_, ds_) ->
          let _ =
            TypeCheck.typeCheck
              ( F.makectx (I.Decl (psi_, F.Block b_)),
                (I.Uni I.Type, I.Uni I.Kind) )
          in
          let psi'_, delta'_, s' =
            assume (I.Decl (psi_, F.Block b_), shiftBlock (b_, delta_), ds_)
          in
          (raiseType (b_, psi'_), raiseM (b_, delta'_), s')
      | psi_, delta_, F.App ((kk, u_), ds_) -> begin
          match infer (delta_, kk) with
          | F.MDec (name, F.All (F.Prim (I.Dec (_, v_)), f_)), s ->
              let _ =
                try TypeCheck.typeCheck (F.makectx psi_, (u_, I.EClo (v_, s)))
                with TypeCheck.Error msg ->
                  raise
                    (Error
                       ((((((msg ^ " ") ^ Print.expToString (F.makectx psi_, u_))
                          ^ " has type ")
                         ^ Print.expToString
                             ( F.makectx psi_,
                               TypeCheck.infer' (F.makectx psi_, u_) ))
                        ^ " expected ")
                       ^ Print.expToString (F.makectx psi_, I.EClo (v_, s))))
              in
              let dd_ = F.MDec (name, F.forSub (f_, I.Dot (I.Exp u_, s))) in
              let psi'_, delta'_, s' =
                assume (psi_, I.Decl (delta_, dd_), ds_)
              in
              (psi'_, F.mdecSub (dd_, s') :: delta'_, s')
          | F.MDec (name, f_), s ->
              raise
                (Error
                   ("Typecheck Error: Declaration App"
                   ^ FunPrint.forToString (I.Null, f_) [ "x" ]))
        end
      | psi_, delta_, F.PApp ((kk, k), ds_) -> begin
          match infer (delta_, kk) with
          | F.MDec (name, F.All (F.Block (F.CtxBlock (l, g_)), f_)), s ->
              let _ = validBlock (psi_, k, (l, g_)) in
              let dd_ = F.MDec (name, F.forSub (f_, psub (k, g_, s))) in
              let psi'_, delta'_, s' =
                assume (psi_, I.Decl (delta_, dd_), ds_)
              in
              (psi'_, F.mdecSub (dd_, s') :: delta'_, s')
          | _ -> raise (Error "Typecheck Error: Declaration PApp")
        end
      | psi_, delta_, F.Left (kk, ds_) -> begin
          match infer (delta_, kk) with
          | F.MDec (name, F.And (f1_, f2_)), s ->
              let dd_ = F.MDec (name, F.forSub (f1_, s)) in
              let psi'_, delta'_, s' =
                assume (psi_, I.Decl (delta_, dd_), ds_)
              in
              (psi'_, F.mdecSub (dd_, s') :: delta'_, s')
          | _ -> raise (Error "Typecheck Error: Declaration Left")
        end
      | psi_, delta_, F.Right (kk, ds_) -> begin
          match infer (delta_, kk) with
          | F.MDec (name, F.And (f1_, f2_)), s ->
              let dd_ = F.MDec (name, F.forSub (f2_, s)) in
              let psi'_, delta'_, s' =
                assume (psi_, I.Decl (delta_, dd_), ds_)
              in
              (psi'_, F.mdecSub (dd_, s') :: delta'_, s')
          | _ -> raise (Error "Typecheck Error: Declaration Left")
        end
      | psi_, delta_, F.Lemma (cc, ds_) ->
          let (F.LemmaDec (names, _, f_)) = F.lemmaLookup cc in
          let name = foldr (fun (x__op, y__op) -> x__op ^ y__op) "" names in
          let dd_ = F.MDec (Some name, f_) in
          let psi'_, delta'_, s' = assume (psi_, I.Decl (delta_, dd_), ds_) in
          (psi'_, F.mdecSub (dd_, s') :: delta'_, s')

    and checkSub = function
      | I.Null, I.Shift 0, I.Null -> ()
      | I.Decl (psi_, F.Prim d_), I.Shift k, I.Null -> begin
          if k > 0 then checkSub (psi_, I.Shift (k - 1), I.Null)
          else raise (Error "Substitution not well-typed")
        end
      | I.Decl (psi_, F.Block (F.CtxBlock (_, g_))), I.Shift k, I.Null ->
          let g = I.ctxLength g_ in
          begin if k >= g then checkSub (psi_, I.Shift (k - g), I.Null)
          else raise (Error "Substitution not well-typed")
          end
      | psi'_, I.Shift k, psi_ ->
          checkSub (psi'_, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), psi_)
      | psi'_, I.Dot (I.Idx k, s'), I.Decl (psi_, F.Prim (I.Dec (_, v2_))) ->
          let g'_ = F.makectx psi'_ in
          let (I.Dec (_, v1_)) = I.ctxDec (g'_, k) in
          begin if Conv.conv ((v1_, I.id), (v2_, s')) then
            checkSub (psi'_, s', psi_)
          else
            raise
              (Error
                 ((("Substitution not well-typed \n  found: "
                   ^ Print.expToString (g'_, v1_))
                  ^ "\n  expected: ")
                 ^ Print.expToString (g'_, I.EClo (v2_, s'))))
          end
      | psi'_, I.Dot (I.Exp u_, s'), I.Decl (psi_, F.Prim (I.Dec (_, v2_))) ->
          let g'_ = F.makectx psi'_ in
          let _ = TypeCheck.typeCheck (g'_, (u_, I.EClo (v2_, s'))) in
          checkSub (psi'_, s', psi_)
      | ( psi'_,
          (I.Dot (I.Idx k, _) as s),
          I.Decl (psi_, F.Block (F.CtxBlock (l1, g_))) ) ->
          let F.Block (F.CtxBlock (l2, g'_)), w = F.lfctxLFDec (psi'_, k) in
          let rec checkSub' = function
            | (I.Null, w1), s1, I.Null, _ -> s1
            | ( (I.Decl (g'_, I.Dec (_, v'_)), w1),
                I.Dot (I.Idx k', s1),
                I.Decl (g_, I.Dec (_, v_)),
                m ) -> begin
                if k' = m then begin
                  if Conv.conv ((v'_, w1), (v_, s1)) then
                    checkSub' ((g'_, I.comp (w1, I.shift)), s1, g_, m + 1)
                  else raise (Error "ContextBlock assignment not well-typed")
                end
                else raise (Error "ContextBlock assignment out of order")
              end
          in
          checkSub (psi'_, checkSub' ((g'_, w), s, g_, k), psi_)

    and checkOpts = function
      | psi_, delta_, [], _ -> ()
      | psi_, delta_, (psi'_, t, p_) :: o_, (f'_, s') -> begin
          checkSub (psi'_, t, psi_);
          begin
            check (psi'_, deltaSub (delta_, t), p_, (f'_, I.comp (s', t)));
            checkOpts (psi_, delta_, o_, (f'_, s'))
          end
        end

    let rec checkRec (p_, t_) = check (I.Null, I.Null, p_, (t_, I.id))

    let rec isFor = function
      | g_, F.All (F.Prim d_, f_) -> (
          try
            begin
              TypeCheck.checkDec (g_, (d_, I.id));
              isFor (I.Decl (g_, d_), f_)
            end
          with TypeCheck.Error msg -> raise (Error msg))
      | g_, F.All (F.Block (F.CtxBlock (_, g1_)), f_) ->
          isForBlock (g_, F.ctxToList g1_, f_)
      | g_, F.Ex (d_, f_) -> (
          try
            begin
              TypeCheck.checkDec (g_, (d_, I.id));
              isFor (I.Decl (g_, d_), f_)
            end
          with TypeCheck.Error msg -> raise (Error msg))
      | g_, True -> ()
      | g_, F.And (f1_, f2_) -> begin
          isFor (g_, f1_);
          isFor (g_, f2_)
        end

    and isForBlock = function
      | g_, [], f_ -> isFor (g_, f_)
      | g_, d_ :: g1_, f_ -> isForBlock (I.Decl (g_, d_), g1_, f_)

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

    let rec isState (S.State (n, (g_, b_), (ih_, oh_), d, o_, h_, f_)) =
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
              ignore (map (function n', f'_ -> isFor (g_, f'_)) h_);
              isFor (g_, f_)
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

(* # 1 "src/meta/funtypecheck.sml.ml" *)
