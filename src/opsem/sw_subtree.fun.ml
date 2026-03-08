open! Basis

module SwMemoTable (SwMemoTable__0 : sig
  (* structure TableParam : TABLEPARAM *)
  module MemoTable : MEMOTABLE
  module MemoTableInst : MEMOTABLE
end) : MEMOTABLE = struct
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
