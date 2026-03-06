open! Basis;;
(* Abstraction *);;
(* Author: Frank Pfenning, Carsten Schuermann *);;
module type ABSTRACT = sig
                       exception Error of string 
                       val
                         piDepend : ((IntSyn.dec_ * IntSyn.depend_) *
                                     IntSyn.exp_) ->
                                    IntSyn.exp_
                       val
                         closedDec : (IntSyn.dec_
                                      IntSyn.ctx_ *
                                      (IntSyn.dec_ * IntSyn.sub_)) ->
                                     bool
                       val
                         closedSub : (IntSyn.dec_ IntSyn.ctx_ * IntSyn.sub_) ->
                                     bool
                       val
                         closedExp : (IntSyn.dec_
                                      IntSyn.ctx_ *
                                      (IntSyn.exp_ * IntSyn.sub_)) ->
                                     bool
                       val closedCtx : IntSyn.dec_ IntSyn.ctx_ -> bool
                       val closedCTX : Tomega.dec_ IntSyn.ctx_ -> bool
                       val abstractDecImp : IntSyn.exp_ -> int * IntSyn.exp_
                       val
                         abstractDef : (IntSyn.exp_ * IntSyn.exp_) ->
                                       int * (IntSyn.exp_ * IntSyn.exp_)
                       val
                         abstractCtxs : IntSyn.dec_
                                        IntSyn.ctx_
                                        list ->
                                        IntSyn.dec_
                                        IntSyn.ctx_ *
                                        IntSyn.dec_
                                        IntSyn.ctx_
                                        list
                       val
                         abstractTomegaSub : Tomega.sub_ ->
                                             Tomega.dec_
                                             IntSyn.ctx_ *
                                             Tomega.sub_
                       val
                         abstractTomegaPrg : Tomega.prg_ ->
                                             Tomega.dec_
                                             IntSyn.ctx_ *
                                             Tomega.prg_
                       val
                         abstractSpine : (IntSyn.spine_ * IntSyn.sub_) ->
                                         IntSyn.dctx * IntSyn.spine_
                       val
                         collectEVars : (IntSyn.dctx *
                                         IntSyn.eclo *
                                         IntSyn.exp_
                                         list) ->
                                        IntSyn.exp_
                                        list
                       val
                         collectEVarsSpine : (IntSyn.dctx *
                                              (IntSyn.spine_ * IntSyn.sub_) *
                                              IntSyn.exp_
                                              list) ->
                                             IntSyn.exp_
                                             list
                       val
                         raiseTerm : (IntSyn.dctx * IntSyn.exp_) ->
                                     IntSyn.exp_
                       val
                         raiseType : (IntSyn.dctx * IntSyn.exp_) ->
                                     IntSyn.exp_
                       end;;
(* signature ABSTRACT *);;