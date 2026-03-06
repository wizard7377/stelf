# 1 "src/prover/elim.sig.ml"
open! Basis;;
(* ELIM: Version 1.4 *);;
(* Author: Carsten Schuermann *);;
module type ELIM = sig
                   module State : STATE
                   exception Error of string 
                   type nonrec operator
                   val expand : State.focus_ -> operator list
                   val apply : operator -> unit
                   val menu : operator -> string
                   end;;
(* signature ELIM *);;
# 1 "src/prover/elim.fun.ml"
open! Basis;;
(* Elim *);;
(* Author: Carsten Schuermann *);;
(* Date: Thu Mar 16 13:39:26 2006 *);;
module Elim(Elim__0: sig
                     module Data : DATA
                     (*! structure IntSyn' : INTSYN !*)
                     (*! structure Tomega' : TOMEGA !*)
                     (*! sharing Tomega'.IntSyn = IntSyn' !*)
                     module State' : STATE
                     (*! sharing State'.IntSyn = IntSyn' !*)
                     (*! sharing State'.Tomega = Tomega' !*)
                     module Abstract : ABSTRACT
                     (*! sharing Abstract.IntSyn = IntSyn' !*)
                     (*! sharing Abstract.Tomega = Tomega' !*)
                     module TypeCheck : TYPECHECK
                     (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                     module Whnf : WHNF
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     module Unify : UNIFY
                     end) : ELIM
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    (*! structure Tomega = Tomega' !*);;
    module State = State';;
    exception Error of string ;;
    type operator_ = | Local of Tomega.prg_ * int ;;
    type nonrec operator = operator_;;
    open!
      struct
        module S = State;;
        module T = Tomega;;
        module I = IntSyn;;
        exception Success of int ;;
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
        let rec expand (S.Focus ((T.EVar (psi_, r, g_, v_, _, _) as y_), w_))
          =
          let rec matchCtx =
            function 
                     | (null_, _, fs_) -> fs_
                     | (I.Decl (g_, T.PDec (x, f_, _, _)), n, fs_)
                         -> matchCtx (g_, n + 1, ((Local (y_, n)) :: fs_))
                     | (I.Decl (g_, T.UDec _), n, fs_)
                         -> matchCtx (g_, n + 1, fs_)
            in matchCtx (psi_, 1, []);;
        let rec apply =
          function 
                   | Local ((T.EVar (psi_, r, g_, None, None, _) as r_), n)
                       -> let T.PDec (_, f0_, _, _) = T.ctxDec (psi_, n)
                            in begin
                               match f0_
                               with 
                                    | T.All ((T.UDec (I.Dec (_, v_)), _), f_)
                                        -> let x_ =
                                             I.newEVar
                                             (T.coerceCtx (strip psi_), v_)
                                             in let I.NDec x =
                                                  Names.decName
                                                  (T.coerceCtx psi_,
                                                   (I.NDec None))
                                                  in let d_ =
                                                       (T.PDec
                                                        (x,
                                                         T.forSub
                                                         (f_,
                                                          (T.Dot
                                                           ((T.Exp x_), T.id))),
                                                         None, None))
                                                       in let psi'_ =
                                                            (I.Decl
                                                             (psi_, d_))
                                                            in let y_ =
                                                                 T.newEVar
                                                                 (strip psi'_,
                                                                  T.forSub
                                                                  (g_,
                                                                   T.shift))
                                                                 in r :=
                                                                    ((Some
                                                                    ((T.Let
                                                                    (d_,
                                                                    (T.Redex
                                                                    ((T.Var
                                                                    n),
                                                                    (T.AppExp
                                                                    (x_,
                                                                    T.nil_)))),
                                                                    y_)))))
                                    | T.Ex ((d1_, _), f_)
                                        -> let d1'_ =
                                             Names.decName
                                             (T.coerceCtx psi_, d1_)
                                             in let psi'_ =
                                                  (I.Decl
                                                   (psi_, (T.UDec d1'_)))
                                                  in let I.NDec x =
                                                       Names.decName
                                                       (T.coerceCtx psi'_,
                                                        (I.NDec None))
                                                       in let d2_ =
                                                            (T.PDec
                                                             (x, f_, None,
                                                              None))
                                                            in let psi''_ =
                                                                 (I.Decl
                                                                  (psi'_,
                                                                   d2_))
                                                                 in let y_ =
                                                                    T.newEVar
                                                                    (strip
                                                                    psi''_,
                                                                    T.forSub
                                                                    (g_,
                                                                    (T.Shift
                                                                    2)))
                                                                    in 
                                                                    r :=
                                                                    ((Some
                                                                    ((T.LetPairExp
                                                                    (d1'_,
                                                                    d2_,
                                                                    (T.Var n),
                                                                    y_)))))
                                    | true_
                                        -> let y_ =
                                             T.newEVar (strip psi_, g_)
                                             in r :=
                                                  ((Some
                                                    ((T.LetUnit
                                                      ((T.Var n), y_)))))
                               end
                   | Local
                       (T.EVar (psi_, r, T.FClo (f_, s), tc1_, tc2_, x_), n)
                       -> apply
                          ((Local
                            ((T.EVar
                              (psi_, r, T.forSub (f_, s), tc1_, tc2_, x_)),
                             n)));;
        let rec menu (Local ((T.EVar (psi_, _, _, _, _, _) as x_), n)) =
          begin
          match I.ctxLookup (psi_, n)
          with 
               | T.PDec (Some x, _, _, _)
                   -> (("Elim " ^ (TomegaPrint.nameEVar x_)) ^
                         " with variable ")
                        ^ x
          end;;
        end;;
    (* These lines need to move *);;
    (* fun stripTC (T.Abs (_, TC)) = TC *);;
    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *);;
    (* Y is lowered *);;
    (* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *);;
    (* the NONE, NONE may breach an invariant *);;
    (* revisit when we add subterm orderings *);;
    (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *);;
    (* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *);;
    let expand = expand;;
    let apply = apply;;
    let menu = menu;;
    end;;
(*! sharing Unify.IntSyn = IntSyn' !*);;
(* local *);;
(* functor elim *);;
# 1 "src/prover/elim.sml.ml"
