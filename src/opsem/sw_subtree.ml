(* # 1 "src/opsem/sw_subtree.sig.ml" *)
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
    * IntSyn.exp_
    * TableParam.resEqn_
    * TableParam.status_ ->
    TableParam.callCheckResult

  val insertIntoTree :
    IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.exp_
    * TableParam.resEqn_
    * TableParam.answer
    * TableParam.status_ ->
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
    IntSyn.sub_ * TableParam.answer * CompSyn.pskeleton -> TableParam.answState

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

  val memberCtx :
    (IntSyn.dctx * IntSyn.exp_) * IntSyn.dctx -> IntSyn.dec_ option
end
(* signature MemoTable *)

(* # 1 "src/opsem/sw_subtree.fun.ml" *)
open! Basis

module SwMemoTable (SwMemoTable__0 : sig
  (* structure TableParam : TABLEPARAM *)
  module MemoTable : MEMOTABLE
  module MemoTableInst : MEMOTABLE
end) : MEMOTABLE = struct
  open SwMemoTable__0

  (*! structure IntSyn = MemoTable.IntSyn !*)
  (*! structure CompSyn = MemoTable.CompSyn !*)
  (*! structure TableParam = MemoTable.TableParam !*)
  let rec callCheck args =
    begin match !TableParam.strategy with
    | variant_ -> MemoTable.callCheck args
    | subsumption_ -> MemoTableInst.callCheck args
    end

  let rec insertIntoTree args =
    begin match !TableParam.strategy with
    | variant_ -> MemoTable.insertIntoTree args
    | subsumption_ -> MemoTableInst.insertIntoTree args
    end

  let rec answerCheck args =
    begin match !TableParam.strategy with
    | variant_ -> MemoTable.answerCheck args
    | subsumption_ -> MemoTableInst.answerCheck args
    end

  let rec reset () =
    begin match !TableParam.strategy with
    | variant_ -> MemoTable.reset ()
    | subsumption_ -> MemoTableInst.reset ()
    end

  let rec updateTable () =
    begin match !TableParam.strategy with
    | variant_ -> MemoTable.updateTable ()
    | subsumption_ -> MemoTableInst.updateTable ()
    end

  let rec tableSize () =
    begin match !TableParam.strategy with
    | variant_ -> MemoTable.tableSize ()
    | subsumption_ -> MemoTableInst.tableSize ()
    end

  let rec memberCtx args =
    begin match !TableParam.strategy with
    | subsumption_ -> MemoTableInst.memberCtx args
    | variant_ -> MemoTable.memberCtx args
    end
end
(*! sharing MemoTableInst.IntSyn = MemoTable.IntSyn !*)
(*! sharing MemoTableInst.CompSyn = MemoTable.CompSyn !*)
(*! sharing MemoTableInst.TableParam = MemoTable.TableParam !*)
(* functor SwMemoTable *)

(* # 1 "src/opsem/sw_subtree.sml.ml" *)
