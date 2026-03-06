open! Basis;;
(* Recursion *);;
(* Author: Carsten Schuermann *);;
module type RECURSION = sig
                        module MetaSyn : METASYN
                        exception Error of string 
                        type nonrec operator
                        val expandLazy : MetaSyn.state_ -> operator list
                        val expandEager : MetaSyn.state_ -> operator list
                        val apply : operator -> MetaSyn.state_
                        val menu : operator -> string
                        end;;
(* signature RECURSION *);;