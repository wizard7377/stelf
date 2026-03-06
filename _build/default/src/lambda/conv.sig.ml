open! Basis;;
(* Convertibility Modulo Beta and Eta *);;
(* Author: Frank Pfenning, Carsten Schuermann *);;
module type CONV = sig
                   (*! structure IntSyn : INTSYN !*)
                   val conv : (IntSyn.eclo * IntSyn.eclo) -> bool
                   val
                     convDec : ((IntSyn.dec_ * IntSyn.sub_) *
                                (IntSyn.dec_ * IntSyn.sub_)) ->
                               bool
                   val convSub : (IntSyn.sub_ * IntSyn.sub_) -> bool
                   end;;
(* signature CONV *);;