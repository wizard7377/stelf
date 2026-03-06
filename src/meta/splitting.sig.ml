open! Basis;;
(* Splitting : Version 1.3 *);;
(* Author: Carsten Schuermann *);;
module type MTPSPLITTING = sig
                           module StateSyn : STATESYN
                           exception Error of string 
                           type nonrec operator
                           val expand : StateSyn.state_ -> operator list
                           val applicable : operator -> bool
                           val apply : operator -> StateSyn.state_ list
                           val menu : operator -> string
                           val index : operator -> int
                           val compare : (operator * operator) -> order
                           end;;
(* signature MTPSPLITTING *);;