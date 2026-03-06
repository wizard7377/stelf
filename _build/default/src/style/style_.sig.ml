open! Basis;;
(* Style Checking *);;
(* Author: Carsten Schuermann *);;
module type STYLECHECK = sig
                         exception Error of string 
                         val check : unit -> unit
                         (* raises Error (msg) *)
                         val checkConDec : IntSyn.cid -> unit
                         end;;
(* signature STYLECHECK *);;