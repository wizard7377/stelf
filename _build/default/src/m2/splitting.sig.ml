open! Basis;;
(* Splitting *);;
(* Author: Carsten Schuermann *);;
module type SPLITTING = sig
                        module MetaSyn : METASYN
                        exception Error of string 
                        type nonrec operator
                        val expand : MetaSyn.state_ -> operator list
                        val apply : operator -> MetaSyn.state_ list
                        val var : operator -> int
                        val menu : operator -> string
                        val index : operator -> int
                        end;;
(* signature SPLITTING *);;