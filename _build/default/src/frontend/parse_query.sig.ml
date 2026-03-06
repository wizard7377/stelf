open! Basis;;
(* Parsing Queries *);;
(* Author: Frank Pfenning *);;
module type PARSE_QUERY = sig
                          (*! structure Parsing : PARSING !*)
                          module ExtQuery : EXTQUERY
                          val parseQuery' : ExtQuery.query Parsing.parser
                          val
                            parseSolve' : (ExtQuery.define
                                           list *
                                           ExtQuery.solve)
                            Parsing.parser
                          end;;
(* signature PARSE_QUERY *);;