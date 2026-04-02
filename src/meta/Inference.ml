(* # 1 "src/meta/Inference.sig.ml" *)
open! Basis
open MtpGlobal
open Funtypecheck
open Uniquesearch
open Funprint
open Funsyn
open Statesyn

(* Inference: Version 1.3 *)
(* Author: Carsten Schuermann *)
include Inference_intf
(* signature Inference *)

(* # 1 "src/meta/Inference.fun.ml" *)
open! Global
open! Basis

(* Inference:  Version 1.3*)
(* Author: Carsten Schuermann *)
module Inference (Inference__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn !*)
  module StateSyn' : Statesyn_intf.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn !*)
  module FunTypeCheck : Funtypecheck_intf.FUNTYPECHECK

  (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
  module UniqueSearch : Uniquesearch_intf.UNIQUESEARCH

  (*! sharing UniqueSearch.IntSyn = IntSyn !*)
  (*! sharing UniqueSearch.FunSyn = FunSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module Whnf : WHNF
end) : Inference_intf.INFERENCE = struct
  (*! structure FunSyn = FunSyn' !*)
  open Inference__0
  module StateSyn = StateSyn'

  exception Error of string

  type nonrec operator = unit -> StateSyn.state

  open! struct
    module S = StateSyn
    module F = FunSyn
    module I = IntSyn

    exception Success

    let rec createEVars = function
      | g_, (I.Pi ((I.Dec (_, v_), meta_), v'_), s) ->
          let x_ = I.newEVar (g_, I.EClo (v_, s)) in
          let x'_ = Whnf.lowerEVar x_ in
          let xs_, fVs'_ = createEVars (g_, (v'_, I.Dot (I.Exp x_, s))) in
          (x'_ :: xs_, fVs'_)
      | g_, ((_, s) as fVs_) -> ([], fVs_)

    let rec forward = function
      | g_, b_, (I.Pi ((_, meta_), _) as v_) -> (
          let _ =
            begin if !Global.doubleCheck then
              TypeCheck.typeCheck (g_, (v_, I.Uni I.Type))
            else ()
            end
          in
          let xs_, (v'_, s') = createEVars (g_, (v_, I.id)) in
          try
            begin match
              UniqueSearch.searchEx
                ( 2,
                  xs_,
                  function
                  | [] -> [ Whnf.normalize (v'_, s') ]
                  | _ -> raise (UniqueSearch.Error "Too many solutions") )
            with
            | vf''_ :: [] -> Some vf''_
            | [] -> None
            end
          with UniqueSearch.Error _ -> None)
      | g_, b_, v_ -> None

    let rec expand' = function
      | (g0_, b0_), (I.Null, I.Null), n ->
          ((I.Null, I.Null), function (g'_, b'_), w' -> ((g'_, b'_), w'))
      | ( (g0_, b0_),
          (I.Decl (g_, (I.Dec (_, v_) as d_)), I.Decl (b_, (S.Lemma rl_ as t_))),
          n ) ->
          let (g0'_, b0'_), sc' = expand' ((g0_, b0_), (g_, b_), n + 1) in
          let s = I.Shift (n + 1) in
          let vs_ = Whnf.normalize (v_, s) in
          begin match forward (g0_, b0_, vs_) with
          | None -> ((I.Decl (g0'_, d_), I.Decl (b0'_, t_)), sc')
          | Some v'_ ->
              ( (I.Decl (g0'_, d_), I.Decl (b0'_, S.Lemma S.RLdone)),
                function
                | (g'_, b'_), w' ->
                    let v''_ = Whnf.normalize (v'_, w') in
                    sc'
                      ( ( I.Decl (g'_, I.Dec (None, v''_)),
                          I.Decl (b'_, S.Lemma (S.Splits !MTPGlobal.maxSplit))
                        ),
                        I.comp (w', I.shift) ) )
          end
      | gb0_, (I.Decl (g_, d_), I.Decl (b_, t_)), n ->
          let (g0'_, b0'_), sc' = expand' (gb0_, (g_, b_), n + 1) in
          ((I.Decl (g0'_, d_), I.Decl (b0'_, t_)), sc')

    let rec expand (S.State (n, (g_, b_), (ih_, oh_), d, o_, h_, f_) as s_) =
      let _ =
        begin if !Global.doubleCheck then TypeCheck.typeCheckCtx g_ else ()
        end
      in
      let (gnew_, bnew_), sc = expand' ((g_, b_), (g_, b_), 0) in
      let _ =
        begin if !Global.doubleCheck then TypeCheck.typeCheckCtx gnew_ else ()
        end
      in
      let (g'_, b'_), w' = sc ((gnew_, bnew_), I.id) in
      let _ = TypeCheck.typeCheckCtx g'_ in
      let s'_ =
        S.State
          ( n,
            (g'_, b'_),
            (ih_, oh_),
            d,
            S.orderSub (o_, w'),
            map (function i, f'_ -> (i, F.forSub (f'_, w'))) h_,
            F.forSub (f_, w') )
      in
      let _ =
        begin if !Global.doubleCheck then FunTypeCheck.isState (Obj.magic s'_)
        else ()
        end
      in
      function () -> s'_

    let rec apply f = f ()
    let rec menu _ = "Inference"
  end

  (* createEVars (G, (F, V, s)) = (Xs', (F', V', s'))

       Invariant:
       If   |- G ctx
       and  G0 |- F = {{x1:A1}} .. {{xn::An}} F1 formula
       and  G0 |- V = { x1:A1}  .. {xn:An} V1 : type
       and  G |- s : G0
       then Xs' = (X1', .., Xn') a list of EVars
       and  G |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  G |- s: G'
       and  G0 |- F' = F1 for
       and  G0 |- V' = V1 : type
    *)
  (* forward (G, B, (V, F)) = (V', F')  (or none)

       Invariant:
       If   |- G ctx
       and  G |- B tags
       and  G |- V type
       and  G; . |- F : formula
       then G |- V' type
       and  G; . |- F' : formula

    *)
  (* expand' ((G, B), n) = ((Gnew, Bnew), sc)

       Invariant:
       If   |- G0 ctx    G0 |- B0 tags
       and  |- G ctx     G |- B tags
       and  G prefix of G0 , and B prefix of B0
       and  n + |G| = |G0|
       then sc is a continutation which maps
            |- G' ctx
            and G' |- B' tags
            and G', B' |- w' : G0, B0
            to  |- G'' ctx
            and G'' |- B'' tags
            and G'', B'' extends G, B
       and |- Gnew = G ctx
       and Gnew |- Bnew tags
       where Bnew stems from B where all used lemmas (S.RL) are now tagged with (S.RLdone)
    *)
  (* G' |- V'' : type *)
  (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
  (* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
  (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
  let expand = expand
  let apply = apply
  let menu = menu
end
(*! sharing Whnf.IntSyn = IntSyn !*)
(* local *)
(* functor Filling *)

(* # 1 "src/meta/Inference.sml.ml" *)
