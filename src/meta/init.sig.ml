open! Basis;;
(* Initialization *);;
(* Author: Carsten Schuermann *);;
module type MTPINIT = sig
                      (*! structure FunSyn : FUNSYN !*)
                      module StateSyn : STATESYN
                      exception Error of string 
                      (* Current restriction to non-mutual inductive theorems ! *)
                      val
                        init : (FunSyn.for_ * StateSyn.order_) ->
                               StateSyn.state_
                               list
                      end;;
(* signature MTPINIT *);;