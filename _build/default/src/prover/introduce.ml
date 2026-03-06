# 1 "src/prover/introduce.sig.ml"
open! Basis;;
(* Introduce: Version 1.4 *);;
(* Author: Carsten Schuermann *);;
module type INTRODUCE = sig
                        (*! structure IntSyn : INTSYN !*)
                        (*! structure Tomega : TOMEGA !*)
                        module State : STATE
                        exception Error of string 
                        type nonrec operator
                        val expand : State.focus_ -> operator option
                        val apply : operator -> unit
                        val menu : operator -> string
                        end;;
(* signature INTRODUCE *);;
# 1 "src/prover/introduce.fun.ml"
open! Basis;;
module Introduce(Introduce__0: sig
                               (* Introduce *)
                               (* Author: Carsten Schuermann *)
                               (*! structure IntSyn' : INTSYN !*)
                               (*! structure Tomega' : TOMEGA !*)
                               (*! sharing Tomega'.IntSyn = IntSyn' !*)
                               module State' : STATE
                               module TomegaNames : TOMEGANAMES
                               end) : INTRODUCE
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    (*! structure Tomega = Tomega' !*);;
    module State = State';;
    open!
      struct
        module S = State';;
        module T = Tomega;;
        module I = IntSyn;;
        exception Error = S.Error;;
        type nonrec operator = T.prg_ * T.prg_;;
        let rec stripTC tc_ = tc_;;
        let rec stripTCOpt =
          function 
                   | None -> None
                   | Some tc_ -> (Some (stripTC tc_));;
        let rec stripDec =
          function 
                   | T.UDec d_ -> (T.UDec d_)
                   | T.PDec (name, f_, tc1_, tc2_)
                       -> (T.PDec (name, f_, tc1_, stripTCOpt tc2_));;
        let rec strip =
          function 
                   | null_ -> I.null_
                   | I.Decl (psi_, d_) -> (I.Decl (strip psi_, stripDec d_));;
        let rec expand =
          function 
                   | S.Focus
                       ((T.EVar (psi_, r, T.All ((d_, _), f_), None, None, _)
                          as r_),
                        w_)
                       -> let d'_ = TomegaNames.decName (psi_, d_)
                            in (Some
                                (r_,
                                 (T.Lam
                                  (d'_,
                                   T.newEVar ((I.Decl (strip psi_, d'_)), f_)))))
                   | S.Focus
                       ((T.EVar
                          (psi_, r, T.Ex (((I.Dec (_, v_) as d_), _), f_),
                           None, None, _)
                          as r_),
                        w_)
                       -> let x_ = I.newEVar (T.coerceCtx psi_, v_)
                            in let y_ =
                                 T.newEVar
                                 (psi_,
                                  T.forSub (f_, (T.Dot ((T.Exp x_), T.id))))
                                 in (Some (r_, (T.PairExp (x_, y_))))
                   | S.Focus
                       ((T.EVar (psi_, r, true_, None, None, _) as r_), w_)
                       -> (Some (r_, T.unit_))
                   | S.Focus
                       (T.EVar (psi_, r, T.FClo (f_, s), tc1_, tc2_, x_), w_)
                       -> expand
                          ((S.Focus
                            ((T.EVar
                              (psi_, r, T.forSub (f_, s), tc1_, tc2_, x_)),
                             w_)))
                   | S.Focus (T.EVar (psi_, r, _, _, _, _), w_) -> None;;
        let rec apply (T.EVar (_, r, _, _, _, _), p_) = r := ((Some p_));;
        let rec menu (r, p_) = "Intro " ^ (TomegaPrint.nameEVar r);;
        end;;
    (*    fun stripTC (T.Abs (_, TC)) = TC *);;
    (* expand S = S'

       Invariant:
       If   S = (Psi |> all x1:A1 .... xn: An. F)
       and  F does not start with an all quantifier
       then S' = (Psi, x1:A1, ... xn:An |> F)
    *);;
    (* apply O = S

       Invariant:
       O = S
    *);;
    (* need to trail for back *);;
    (* menu O = s

       Invariant:
       s = ""Apply universal introduction rules""
    *);;
    exception Error = Error;;
    type nonrec operator = operator;;
    let expand = expand;;
    let apply = apply;;
    let menu = menu;;
    end;;
(*! sharing State'.IntSyn = IntSyn' !*);;
(*! sharing State'.Tomega = Tomega' !*);;
# 1 "src/prover/introduce.sml.ml"
