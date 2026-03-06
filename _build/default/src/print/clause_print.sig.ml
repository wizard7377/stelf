open! Basis;;
(* Clause Printing *);;
(* Author: Frank Pfenning, Carsten Schuermann *);;
module type CLAUSEPRINT = sig
                          (*! structure IntSyn : INTSYN !*)
                          module Formatter : FORMATTER
                          val
                            formatClause : (IntSyn.dctx * IntSyn.exp_) ->
                                           Formatter.format
                          val
                            formatConDec : IntSyn.conDec_ -> Formatter.format
                          val
                            clauseToString : (IntSyn.dctx * IntSyn.exp_) ->
                                             string
                          val conDecToString : IntSyn.conDec_ -> string
                          val printSgn : unit -> unit
                          end;;
(* signature CLAUSEPRINT *);;