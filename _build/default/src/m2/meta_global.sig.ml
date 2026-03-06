open! Basis;;
(* Global parameters *);;
(* Author: Carsten Schuermann *);;
module type METAGLOBAL = sig
                         type strategy_ = | Rfs 
                                          | Frs 
                         val strategy : strategy_ ref
                         val maxFill : int ref
                         val maxSplit : int ref
                         val maxRecurse : int ref
                         end;;
(* signature METAGLOBAL *);;