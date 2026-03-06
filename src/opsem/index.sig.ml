open! Basis;;
(* Indexing *);;
(* Author: Brigitte Pientka *);;
module type TABLEINDEX = sig
                         (*! structure IntSyn : INTSYN !*)
                         (*! structure CompSyn : COMPSYN !*)
                         type nonrec __0 = {
                           solutions: ((IntSyn.dctx * IntSyn.sub_) *
                                       CompSyn.pskeleton)
                             list ;
                           lookup: int }
                         type nonrec answer = __0
                         type strategy_ = | Variant 
                                          | Subsumption 
                         val strategy : strategy_ ref
                         val termDepth : int option ref
                         val ctxDepth : int option ref
                         val ctxLength : int option ref
                         val strengthen : bool ref
                         val
                           query : (IntSyn.dctx *
                                    IntSyn.dctx *
                                    IntSyn.exp_ *
                                    IntSyn.sub_ *
                                    (CompSyn.pskeleton -> unit))
                           option ref
                         type answState = | New 
                                          | Repeated 
                         (* table: G, Gdprog |- goal , 
            (answ list (ith stage) , answ list (1 to i-1 th stage))
   *)
                         val
                           table : ((int
                                     ref *
                                     IntSyn.dctx *
                                     IntSyn.dctx *
                                     IntSyn.exp_) *
                                    answer)
                           list ref
                         val
                           noAnswers : ((IntSyn.dctx *
                                         IntSyn.dctx *
                                         IntSyn.exp_) *
                                        answer)
                                       list ->
                                       bool
                         (* call check/insert *)
                         (* callCheck (G, D, U)
   *
   * if D, G |- U     in table  
   *    then SOME(entries)
   * if D, G |- U not in table 
   *    then NONE  
   *          SIDE EFFECT: D, G |- U added to table
   *)
                         val
                           callCheck : (IntSyn.dctx *
                                        IntSyn.dctx *
                                        IntSyn.exp_) ->
                                       ((IntSyn.dctx *
                                         IntSyn.dctx *
                                         IntSyn.exp_) *
                                        answer)
                                       list
                                       option
                         (* answer check/insert *)
                         (* answerCheck (G, D, (U,s))
   * 
   * Assumption: D, G |- U is in table
   *             and A represents the corresponding solutions
   * 
   * G |- s : D, G
   * Dk, G |- sk : D, G
   *
   * If  (Dk, sk) in A then repeated
   *  else New
   *)
                         val
                           answerCheck : (IntSyn.dctx *
                                          IntSyn.dctx *
                                          IntSyn.exp_ *
                                          IntSyn.sub_ *
                                          CompSyn.pskeleton) ->
                                         answState
                         (* reset table *)
                         val reset : unit -> unit
                         val printTable : unit -> unit
                         val printTableEntries : unit -> unit
                         (* updateTable 
   *
   * SIDE EFFECT: 
   *   for each table entry: 
   *       advance lookup pointer
   *
   * if Table did not change during last stage 
   *    then updateTable () =  false
   * else updateTable () = true
   *)
                         val updateTable : unit -> bool
                         val
                           solutions : answer ->
                                       ((IntSyn.dctx * IntSyn.sub_) *
                                        CompSyn.pskeleton)
                                       list
                         val lookup : answer -> int
                         end;;
(* signature TABLEINDEX *);;