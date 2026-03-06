open! Basis;;
(* Printing of functional proof terms *);;
(* Author: Carsten Schuermann *);;
module type FUNPRINT = sig
                       (*! structure FunSyn : FUNSYN !*)
                       module Formatter : FORMATTER
                       val
                         formatForBare : (IntSyn.dctx * FunSyn.for_) ->
                                         Formatter.format
                       val
                         formatFor : (FunSyn.lfctx * FunSyn.for_) ->
                                     string
                                     list ->
                                     Formatter.format
                       val
                         formatPro : (FunSyn.lfctx * FunSyn.pro_) ->
                                     string
                                     list ->
                                     Formatter.format
                       val
                         formatLemmaDec : FunSyn.lemmaDec_ ->
                                          Formatter.format
                       val
                         forToString : (FunSyn.lfctx * FunSyn.for_) ->
                                       string
                                       list ->
                                       string
                       val
                         proToString : (FunSyn.lfctx * FunSyn.pro_) ->
                                       string
                                       list ->
                                       string
                       val lemmaDecToString : FunSyn.lemmaDec_ -> string
                       end;;
(* signature PRINT *);;