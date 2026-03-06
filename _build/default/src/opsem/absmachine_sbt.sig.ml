open! Basis;;
(* Abstract Machine *);;
(* Author: Iliano Cervesato *);;
(* Modified: Jeff Polakow *);;
(* Modified: Frank Pfenning *);;
module type ABSMACHINESBT = sig
                            (*! structure IntSyn  : INTSYN !*)
                            (*! structure CompSyn : COMPSYN !*)
                            val
                              solve : ((CompSyn.goal_ * IntSyn.sub_) *
                                       CompSyn.dProg_ *
                                       (CompSyn.flatterm_ list -> unit)) ->
                                      unit
                            end;;
(* signature ABSMACHINESBT *);;