open! Basis;;
(* Syntax for elaborated modules *);;
(* Author: Kevin Watkins *);;
module type MODSYN = sig
                     (*! structure IntSyn : INTSYN !*)
                     module Names : NAMES
                     (*! structure Paths : PATHS !*)
                     exception Error of string 
                     val
                       abbrevify : (IntSyn.cid * IntSyn.conDec_) ->
                                   IntSyn.conDec_
                     val strictify : IntSyn.conDec_ -> IntSyn.conDec_
                     type nonrec module_
                     (*
  type action = IntSyn.cid * (string * Paths.occConDec option) -> unit
  type transform = IntSyn.cid * IntSyn.ConDec -> IntSyn.ConDec
  *)
                     val
                       installStruct : ((IntSyn.strDec_ *
                                         module_ *
                                         Names.namespace
                                         option *
                                         ((IntSyn.cid *
                                           (string * Paths.occConDec option)) ->
                                          unit) *
                                         bool) ->
                                        unit(* action *))
                     val
                       installSig : ((module_ *
                                      Names.namespace
                                      option *
                                      ((IntSyn.cid *
                                        (string * Paths.occConDec option)) ->
                                       unit) *
                                      bool) ->
                                     unit(* action *))
                     val
                       instantiateModule : ((module_ *
                                             (Names.namespace ->
                                              (IntSyn.cid * IntSyn.conDec_) ->
                                              IntSyn.conDec_)) ->
                                            module_(* Names.namespace -> transform *))
                     (* Extract some entries of the current global signature table in order
     to create a self-contained module.
  *)
                     val
                       abstractModule : (Names.namespace * IntSyn.mid option) ->
                                        module_
                     val reset : unit -> unit
                     val installSigDef : (string * module_) -> unit
                     (* Error if would shadow *)
                     val lookupSigDef : string -> module_ option
                     val sigDefSize : unit -> int
                     val resetFrom : int -> unit
                     end;;