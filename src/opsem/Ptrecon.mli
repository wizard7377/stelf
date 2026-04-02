include module type of Ptrecon_intf

module PtRecon (PtRecon__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Assign : ASSIGN

  (*! sharing Assign.IntSyn = IntSyn' !*)
  (*! structure TableParam : TABLEPARAM !*)
  module MemoTable : MemoTable_intf.MEMOTABLE

  (*! sharing MemoTable.TableParam = TableParam !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  (* CPrint currently unused *)
  module CPrint : Cprint.CPRINT

  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn' !*)
  module Names : NAMES
end) : PTRECON
