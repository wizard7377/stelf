open! Basis;;
(* Global Table parameters *);;
(* Author: Brigitte Pientka *);;
module type TABLEPARAM = sig
                         (*! structure IntSyn : INTSYN !*)
                         (*! structure CompSyn : COMPSYN !*)
                         (*! structure RBSet : RBSET !*)
                         exception Error of string 
                         (* Residual equation *)
                         type resEqn_ =
                           | Trivial 
                           | Unify of
                             IntSyn.dctx *
                             IntSyn.exp_ *
                             IntSyn.exp_ *
                             (resEqn_(* call unify *)) 
                         (* trivially done *)
                         type nonrec __0 = {
                           solutions: ((IntSyn.dctx * IntSyn.sub_) *
                                       CompSyn.pskeleton)
                             list ;
                           lookup: int }
                         type nonrec answer = __0 ref
                         type status_ = | Complete 
                                        | Incomplete 
                         val
                           globalTable : (IntSyn.dctx *
                                          IntSyn.dctx *
                                          IntSyn.dctx *
                                          IntSyn.exp_ *
                                          resEqn_ *
                                          answer *
                                          status_)
                           list ref
                         val resetGlobalTable : unit -> unit
                         val emptyAnsw : unit -> answer
                         (* destructively updates answers *)
                         val
                           addSolution : (((IntSyn.dctx * IntSyn.sub_) *
                                           CompSyn.pskeleton) *
                                          answer) ->
                                         unit
                         val updateAnswLookup : (int * answer) -> unit
                         val
                           solutions : answer ->
                                       ((IntSyn.dctx * IntSyn.sub_) *
                                        CompSyn.pskeleton)
                                       list
                         val lookup : answer -> int
                         val noAnswers : answer -> bool
                         (* ---------------------------------------------------------------------- *)
                         type nonrec asub = IntSyn.exp_ RBSet.ordSet
                         val aid : unit -> asub
                         type callCheckResult =
                           | NewEntry of answer 
                           | RepeatedEntry of
                             (IntSyn.sub_ * IntSyn.sub_) * answer * status_ 
                           | DivergingEntry of IntSyn.sub_ * answer 
                         type answState = | New_ 
                                          | Repeated_ 
                         (* ---------------------------------------------------------------------- *)
                         type strategy_ = | Variant 
                                          | Subsumption 
                         val strategy : strategy_ ref
                         val stageCtr : int ref
                         val divHeuristic : bool ref
                         val termDepth : int option ref
                         val ctxDepth : int option ref
                         val ctxLength : int option ref
                         val strengthen : bool ref
                         end;;
(* signature TABLEPARAM *);;