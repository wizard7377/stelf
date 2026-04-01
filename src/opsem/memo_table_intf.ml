(* # 1 "src/opsem/memo_table.sig.ml" *)
open! Basis
open Table_param

(* Indexing *)
(* Author: Brigitte Pientka *)

module type MEMOTABLE = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  (*! structure TableParam : TABLEPARAM !*)
  (* call check/insert *)
  (* callCheck (G, D, U, eqn)
   *
   * if D, G |- U & eqn     in table  then RepeatedEntry (entries)
   * if D, G |- U & eqn not in table  then NewEntry (ptrAnswer)
   * SIDE EFFECT: D, G |- U added to table
   *)
  val callCheck :
    IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.exp
    * TableParam.resEqn
    * TableParam.status ->
    TableParam.callCheckResult

  (* answer check/insert *)
  (* answerCheck (G, D, (U,s))
   * 
   * Assupmtion: D, G |- U is in table
   *             and A represents the corresponding solutions
   * 
   * G |- s : D, G
   * Dk, G |- sk : D, G
   *
   * If  (Dk, sk) in A then repeated
   *  else new
   *)
  val answerCheck :
    IntSyn.sub * TableParam.answer * CompSyn.pskeleton -> TableParam.answState

  (* reset table *)
  val reset : unit -> unit

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
  val tableSize : unit -> int
  val memberCtx : (IntSyn.dctx * IntSyn.exp) * IntSyn.dctx -> IntSyn.dec option

  val insertIntoTree :
    IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.exp
    * TableParam.resEqn
    * TableParam.answer
    * TableParam.status ->
    TableParam.callCheckResult
end
