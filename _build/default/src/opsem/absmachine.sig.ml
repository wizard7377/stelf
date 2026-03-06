open! Basis;;
(* Abstract Machine *);;
(* Author: Iliano Cervesato *);;
(* Modified: Jeff Polakow *);;
(* Modified: Frank Pfenning *);;
module type ABSMACHINE = sig
                         (*! structure IntSyn : INTSYN !*)
                         (*! structure CompSyn : COMPSYN !*)
                         val
                           solve : ((CompSyn.goal_ * IntSyn.sub_) *
                                    CompSyn.dProg_ *
                                    (IntSyn.exp_ -> unit)) ->
                                   unit
                         end;;
(* signature ABSMACHINE *);;