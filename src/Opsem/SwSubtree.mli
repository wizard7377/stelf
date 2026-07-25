include module type of SWSUBTREE

module SwMemoTable (SwMemoTable__0 : sig
  (* structure TableParam : TABLEPARAM *)
  module MemoTable : MEMOTABLE.MEMOTABLE
  module MemoTableInst : MEMOTABLE.MEMOTABLE
end) : MEMOTABLE.MEMOTABLE
