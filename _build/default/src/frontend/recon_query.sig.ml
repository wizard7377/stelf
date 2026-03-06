open! Basis;;
(* External Syntax for queries *);;
(* Author: Frank Pfenning *);;
module type EXTQUERY = sig
                       module ExtSyn : EXTSYN
                       (*! structure Paths : PATHS !*)
                       type nonrec query
                       (* query *)
                       val query : (string option * ExtSyn.term) -> query
                       (* ucid : tm | tm *)
                       type nonrec define
                       val
                         define : (string
                                   option *
                                   ExtSyn.term *
                                   ExtSyn.term
                                   option) ->
                                  define
                       type nonrec solve
                       val
                         solve : (string option * ExtSyn.term * Paths.region) ->
                                 solve
                       end;;
(* id : tm | _ : tm *);;
(* signature EXTQUERY *);;
module type RECON_QUERY = sig
                          (*! structure IntSyn : INTSYN !*)
                          include EXTQUERY
                          exception Error of string 
                          val
                            queryToQuery : (query * Paths.location) ->
                                           IntSyn.exp_ *
                                           string
                                           option *
                                           (IntSyn.exp_ * string)
                                           list
                          (* (A, SOME(""X""), [(Y1, ""Y1""),...] *)
                          (* where A is query type, X the optional proof term variable name *)
                          (* Yi the EVars in the query and ""Yi"" their names *)
                          val
                            solveToSolve : (define
                                            list *
                                            solve *
                                            Paths.location) ->
                                           IntSyn.exp_ *
                                           (IntSyn.exp_ ->
                                            (IntSyn.conDec_ *
                                             Paths.occConDec
                                             option)
                                            list)
                          end;;
(* signature RECON_QUERY *);;