open! Basis;;
(* External syntax for module expressions *);;
(* Author: Kevin Watkins *);;
module type MODEXTSYN = sig
                        module ExtSyn : EXTSYN
                        (*! structure Paths : PATHS !*)
                        type nonrec strexp
                        val
                          strexp : (string list * string * Paths.region) ->
                                   strexp
                        type nonrec inst
                        val
                          coninst : ((string list * string * Paths.region) *
                                     ExtSyn.term *
                                     Paths.region) ->
                                    inst
                        val
                          strinst : ((string list * string * Paths.region) *
                                     strexp *
                                     Paths.region) ->
                                    inst
                        type nonrec sigexp
                        val thesig : sigexp
                        val sigid : (string * Paths.region) -> sigexp
                        val wheresig : (sigexp * inst list) -> sigexp
                        type nonrec sigdef
                        val sigdef : (string option * sigexp) -> sigdef
                        type nonrec structdec
                        val structdec : (string option * sigexp) -> structdec
                        val structdef : (string option * strexp) -> structdec
                        end;;
module type RECON_MODULE = sig
                           include MODEXTSYN
                           module ModSyn : MODSYN
                           exception Error of string 
                           type nonrec whereclause
                           type structDec_ =
                             | StructDec of
                               string
                               option *
                               ModSyn.module_ *
                               whereclause
                               list 
                             | StructDef of string option * IntSyn.mid 
                           val strexpToStrexp : strexp -> IntSyn.mid
                           val
                             sigexpToSigexp : (sigexp * ModSyn.module_ option) ->
                                              ModSyn.module_ *
                                              whereclause
                                              list
                           val
                             sigdefToSigdef : (sigdef * ModSyn.module_ option) ->
                                              string
                                              option *
                                              ModSyn.module_ *
                                              whereclause
                                              list
                           val
                             structdecToStructDec : (structdec *
                                                     ModSyn.module_
                                                     option) ->
                                                    structDec_
                           val
                             moduleWhere : (ModSyn.module_ * whereclause) ->
                                           ModSyn.module_
                           end;;