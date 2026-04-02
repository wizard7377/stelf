include module type of SwSubtree_intf

module SwMemoTable (SwMemoTable__0 : sig
  (* structure TableParam : TABLEPARAM *)
  module MemoTable : MemoTable_intf.MEMOTABLE
  module MemoTableInst : MemoTable_intf.MEMOTABLE
end) : MemoTable_intf.MEMOTABLE
