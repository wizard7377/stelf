open! Basis
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Formatter
open! Formatter__Formatter_
open! Index
open! Index.Index_
open! Typecheck
open! Typecheck.Typecheck_
open! Solvers
open! Solvers.Solvers_
open! Subordinate
open! Subordinate
open! Compile
open! Compile.Compile_
open! CompSyn
open! Assign
open! Tabling

(* # 1 "src/opsem/SwSubtree.sig.ml" *)
open! Basis
open TableParam

(* Indexing *)
(* Author: Brigitte Pientka *)
include SWSUBTREE
(* signature MemoTable *)

(* # 1 "src/opsem/SwSubtree.fun.ml" *)
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
  let callCheck args =
    begin match !TableParam.strategy with
    | Variant -> MemoTable.callCheck args
    | Subsumption -> MemoTableInst.callCheck args
    end

  let insertIntoTree args =
    begin match !TableParam.strategy with
    | Variant -> MemoTable.insertIntoTree args
    | Subsumption -> MemoTableInst.insertIntoTree args
    end

  let answerCheck args =
    begin match !TableParam.strategy with
    | Variant -> MemoTable.answerCheck args
    | Subsumption -> MemoTableInst.answerCheck args
    end

  let reset () =
    begin match !TableParam.strategy with
    | Variant -> MemoTable.reset ()
    | Subsumption -> MemoTableInst.reset ()
    end

  let updateTable () =
    begin match !TableParam.strategy with
    | Variant -> MemoTable.updateTable ()
    | Subsumption -> MemoTableInst.updateTable ()
    end

  let tableSize () =
    begin match !TableParam.strategy with
    | Variant -> MemoTable.tableSize ()
    | Subsumption -> MemoTableInst.tableSize ()
    end

  let memberCtx args =
    begin match !TableParam.strategy with
    | Subsumption -> MemoTableInst.memberCtx args
    | Variant -> MemoTable.memberCtx args
    end
end
(*! sharing MemoTableInst.IntSyn = MemoTable.IntSyn !*)
(*! sharing MemoTableInst.CompSyn = MemoTable.CompSyn !*)
(*! sharing MemoTableInst.TableParam = MemoTable.TableParam !*)
(* functor SwMemoTable *)

(* # 1 "src/opsem/SwSubtree.sml.ml" *)
