(* # 1 "src/opsem/sw_subtree.sig.ml" *)
open! Basis
open Table_param

(* Indexing *)
(* Author: Brigitte Pientka *)
include Sw_subtree_intf
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
    | Variant -> MemoTable.callCheck args
    | Subsumption -> MemoTableInst.callCheck args
    end

  let rec insertIntoTree args =
    begin match !TableParam.strategy with
    | Variant -> MemoTable.insertIntoTree args
    | Subsumption -> MemoTableInst.insertIntoTree args
    end

  let rec answerCheck args =
    begin match !TableParam.strategy with
    | Variant -> MemoTable.answerCheck args
    | Subsumption -> MemoTableInst.answerCheck args
    end

  let rec reset () =
    begin match !TableParam.strategy with
    | Variant -> MemoTable.reset ()
    | Subsumption -> MemoTableInst.reset ()
    end

  let rec updateTable () =
    begin match !TableParam.strategy with
    | Variant -> MemoTable.updateTable ()
    | Subsumption -> MemoTableInst.updateTable ()
    end

  let rec tableSize () =
    begin match !TableParam.strategy with
    | Variant -> MemoTable.tableSize ()
    | Subsumption -> MemoTableInst.tableSize ()
    end

  let rec memberCtx args =
    begin match !TableParam.strategy with
    | Subsumption -> MemoTableInst.memberCtx args
    | Variant -> MemoTable.memberCtx args
    end
end
(*! sharing MemoTableInst.IntSyn = MemoTable.IntSyn !*)
(*! sharing MemoTableInst.CompSyn = MemoTable.CompSyn !*)
(*! sharing MemoTableInst.TableParam = MemoTable.TableParam !*)
(* functor SwMemoTable *)

(* # 1 "src/opsem/sw_subtree.sml.ml" *)
