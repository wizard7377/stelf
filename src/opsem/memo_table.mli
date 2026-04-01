include module type of Memo_table_intf

module MemoTable (MemoTable__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  (*! structure RBSet : RBSET !*)
  (*! structure TableParam : TABLEPARAM !*)
  (*! sharing TableParam.IntSyn = IntSyn' !*)
  (*! sharing TableParam.CompSyn = CompSyn' !*)
  (*! sharing TableParam.RBSet = RBSet !*)
  module AbstractTabled : Abstract_tabled.ABSTRACTTABLED

  (*! sharing AbstractTabled.IntSyn = IntSyn' !*)
  module Print : PRINT
end) : MEMOTABLE
