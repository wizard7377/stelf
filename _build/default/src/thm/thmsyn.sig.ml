open! Basis;;
(* Theorems *);;
(* Author: Carsten Schuermann *);;
(* Modified: Brigitte Pientka *);;
module type THMSYN = sig
                     module Names : NAMES
                     exception Error of string 
                     (*! type Param = string option !*)
                     type order_ =
                       | Varg of string list 
                       | Lex of order_ list 
                       | Simul of order_ list 
                     (* -bp *)
                     type predicate_ = | Less 
                                       | Leq 
                                       | Eq 
                     type redOrder_ =
                       | RedOrder of predicate_ * order_ * order_ 
                     type callpats_ =
                       | Callpats of (IntSyn.cid * string option list) list 
                     (* Termination declaration *)
                     type tDecl_ = | TDecl of order_ * callpats_ 
                     (* -bp *)
                     (* Reduction declaration *)
                     type rDecl_ = | RDecl of redOrder_ * callpats_ 
                     (* Tabled declaration *)
                     type tabledDecl_ = | TabledDecl of IntSyn.cid 
                     (* KeepTable declaration *)
                     type keepTableDecl_ = | KeepTableDecl of IntSyn.cid 
                     (* Theorem declaration  *)
                     type thDecl_ =
                       | ThDecl of
                         (IntSyn.dec_ IntSyn.ctx_ * IntSyn.dec_ IntSyn.ctx_)
                         list *
                         IntSyn.dec_
                         IntSyn.ctx_ *
                         ModeSyn.mode_
                         IntSyn.ctx_ *
                         int 
                     (* Proof declaration *)
                     type pDecl_ = | PDecl of int * tDecl_ 
                     (* World declaration *)
                     (*  datatype WDecl = 
    WDecl of (IntSyn.Dec IntSyn.Ctx * 
	      IntSyn.Dec IntSyn.Ctx) list * Callpats
*)
                     type wDecl_ = | WDecl of Names.qid_ list * callpats_ 
                     val
                       theoremDecToConDec : ((string * thDecl_) *
                                             Paths.region) ->
                                            (IntSyn.dec_
                                             IntSyn.ctx_ *
                                             IntSyn.dec_
                                             IntSyn.ctx_)
                                            list *
                                            IntSyn.conDec_
                     val
                       theoremDecToModeSpine : ((string * thDecl_) *
                                                Paths.region) ->
                                               ModeSyn.modeSpine_
                     end;;
(* signature THMSYN *);;