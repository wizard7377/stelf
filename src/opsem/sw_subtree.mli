include module type of Sw_subtree_intf

module SwMemoTable (SwMemoTable__0 : sig
  (* structure TableParam : TABLEPARAM *)
  module MemoTable : Memo_table.MEMOTABLE
  module MemoTableInst : Memo_table.MEMOTABLE
end) : Memo_table.MEMOTABLE
