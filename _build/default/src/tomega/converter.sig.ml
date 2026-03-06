open! Basis;;
(* Converter from relational representation to a functional
   representation of proof terms *);;
(* Author: Carsten Schuermann *);;
module type CONVERTER = sig
                        (*! structure IntSyn : INTSYN !*)
                        (*! structure Tomega : TOMEGA !*)
                        exception Error of string 
                        exception Error' of Tomega.sub_ 
                        val convertFor : IntSyn.cid list -> Tomega.for_
                        val convertPrg : IntSyn.cid list -> Tomega.prg_
                        val
                          installPrg : (IntSyn.cid
                                        list ->
                                        IntSyn.cid *
                                        Tomega.lemma
                                        list *
                                        Tomega.lemma
                                        list(* projections *))
                        (* selections *)
                        val
                          convertGoal : (Tomega.dec_
                                         IntSyn.ctx_ *
                                         IntSyn.exp_) ->
                                        Tomega.prg_
                        end;;
(* Signature CONVERTER *);;