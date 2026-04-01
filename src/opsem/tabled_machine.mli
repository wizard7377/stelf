include module type of Tabled_machine_intf

module Tabled (Tabled__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module TabledSyn : Tabledsyn.TABLEDSYN

  (*!  sharing TabledSyn.IntSyn = IntSyn' !*)
  module Assign : ASSIGN

  (*!  sharing Assign.IntSyn = IntSyn' !*)
  module Index : INDEX

  (*!  sharing Index.IntSyn = IntSyn' !*)
  module Queue : Queue.QUEUE

  (*! structure TableParam : TABLEPARAM !*)
  (*!  sharing TableParam.IntSyn = IntSyn' !*)
  (*!  sharing TableParam.CompSyn = CompSyn' !*)
  module AbstractTabled : Abstract_tabled.ABSTRACTTABLED

  (*!  sharing AbstractTabled.IntSyn = IntSyn' !*)
  (*! sharing AbstractTabled.TableParam = TableParam !*)
  module MemoTable : Memo_table.MEMOTABLE

  (*!  sharing MemoTable.IntSyn = IntSyn' !*)
  (*!  sharing MemoTable.CompSyn = CompSyn'  !*)
  (*! sharing MemoTable.TableParam = TableParam  !*)
  (* CPrint currently unused *)
  module CPrint : Cprint.CPRINT

  (*!  sharing CPrint.IntSyn = IntSyn' !*)
  (*!  sharing CPrint.CompSyn = CompSyn' !*)
  (* CPrint currently unused *)
  module Print : PRINT
end) : TABLED
