(* # 1 "src/meta/filling.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open Mtp_global
open Mtp_data
open Mtp_search

(* Filling: Version 1.3 *)
(* Author: Carsten Schuermann *)
include Mtp_filling_intf
(* signature MTPFILLING *)

(* # 1 "src/meta/filling.fun.ml" *)
open! Search
open! Global
open! Basis

(* Filling  Version 1.3*)
(* Author: Carsten Schuermann *)
module MTPFilling (MTPFilling__0 : sig
  module MTPGlobal : Mtp_global.MTPGLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn' : FUNSYN !*)
  (*! sharing FunSyn'.IntSyn = IntSyn !*)
  module StateSyn' : Statesyn_intf.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn !*)
  module MTPData : Mtp_data_intf.MTPDATA
  module Search : Mtp_search_intf.MTPSEARCH
  module Whnf : WHNF
end) : Mtp_filling_intf.MTPFILLING = struct
  (*! structure FunSyn = FunSyn' !*)
  open MTPFilling__0
  module StateSyn = StateSyn'

  exception Error of string
  exception TimeOut

  type nonrec operator = unit -> int * FunSyn.pro

  open! struct
    module S = StateSyn
    module F = FunSyn
    module I = IntSyn

    exception Success of int

    let rec createEVars = function
      | g_, (F.True, s) -> ([], F.Unit)
      | g_, (F.Ex (I.Dec (_, v_), f_), s) ->
          let x_ = I.newEVar (g_, I.EClo (v_, s)) in
          let x'_ = Whnf.lowerEVar x_ in
          let xs_, p_ = createEVars (g_, (f_, I.Dot (I.Exp x_, s))) in
          (x'_ :: xs_, F.Inx (x_, p_))

    let rec expand (S.State (n, (g_, b_), (ih_, oh_), d, o_, h_, f_) as s_) =
      let _ =
        begin if !Global.doubleCheck then TypeCheck.typeCheckCtx g_ else ()
        end
      in
      let xs_, p_ = createEVars (g_, (f_, I.id)) in
      function
      | () -> (
          try
            begin
              Search.searchEx
                ( !MTPGlobal.maxFill,
                  xs_,
                  function
                  | max -> begin
                      ignore
                        begin if !Global.doubleCheck then
                          map
                            (function
                              | I.EVar (_, g'_, v_, _) as x_ ->
                                  TypeCheck.typeCheck (g'_, (x_, v_)))
                            xs_
                        else []
                        end;
                      raise (Success max)
                    end );
              raise (Error "Filling unsuccessful")
            end
          with Success max ->
            begin
              MTPData.maxFill := Int.max (!MTPData.maxFill, max);
              (max, p_)
            end)

    let rec apply f = f ()
    let rec menu _ = "Filling   (tries to close this subgoal)"
  end

  (* Checking for constraints: Used to be in abstract, now must be done explicitly! --cs*)
  (* createEVars (G, F) = (Xs', P')

       Invariant:
       If   |- G ctx
       and  G |- F = [[x1:A1]] .. [[xn::An]] formula
       then Xs' = (X1', .., Xn') a list of EVars
       and  G |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  G; D |- P' = <X1', <.... <Xn', <>> ..> in F     for some D
    *)
  (*    fun checkConstraints nil = raise Success
      | checkConstraints (X :: L) =
        if Abstract.closedExp (I.Null, (Whnf.normalize (X, I.id), I.id)) then checkConstraints L
        else ()
*)
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

(* # 1 "src/meta/mtp_filling.sml.ml" *)
