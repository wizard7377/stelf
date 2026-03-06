open! Basis;;
(* Unification on Formulas *);;
(* Author: Carsten Schuermann *);;
module type TOMEGACOVERAGE = sig
                             (*! structure IntSyn : INTSYN !*)
                             (*! structure Tomega : TOMEGA !*)
                             exception Error of string 
                             val
                               coverageCheckPrg : (Tomega.worlds_ *
                                                   Tomega.dec_
                                                   IntSyn.ctx_ *
                                                   Tomega.prg_) ->
                                                  unit
                             end;;
(* Signature TOMEGACOVERAGE *);;