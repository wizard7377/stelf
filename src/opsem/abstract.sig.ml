open! Basis;;
(* Abstraction *);;
(* Author: Brigitte Pientka *);;
module type ABSTRACTTABLED = sig
                             (*! structure IntSyn : INTSYN !*)
                             (*! structure TableParam : TABLEPARAM !*)
                             exception Error of string 
                             val
                               abstractEVarCtx : (CompSyn.dProg_ *
                                                  IntSyn.exp_ *
                                                  IntSyn.sub_) ->
                                                 IntSyn.dctx *
                                                 IntSyn.dctx *
                                                 IntSyn.dctx *
                                                 IntSyn.exp_ *
                                                 TableParam.resEqn_ *
                                                 IntSyn.sub_
                             val
                               abstractAnswSub : IntSyn.sub_ ->
                                                 IntSyn.dctx * IntSyn.sub_
                             val
                               raiseType : (IntSyn.dctx * IntSyn.exp_) ->
                                           IntSyn.exp_
                             end;;
(* signature ABSTRACTTABLED *);;