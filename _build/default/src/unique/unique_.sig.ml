open! Basis;;
(* Uniqueness Checking *);;
(* Author: Frank Pfenning *);;
module type UNIQUE = sig
                     exception Error of string 
                     val
                       checkUnique : (IntSyn.cid * ModeSyn.modeSpine_) ->
                                     unit
                     end;;
(* raises Error(msg) *);;
(* signature UNIQUE *);;