include module type of Thm_intf

module Make_Thm
    (Global : GLOBAL)
    (ThmSyn' : Thmsyn.THMSYN)
    (TabledSyn : Tabledsyn.TABLEDSYN)
    (ModeTable : Modetable.MODETABLE)
    (Order : ORDER)
    (ThmPrint : Thmprint.THMPRINT) :
  THM with module ThmSyn = ThmSyn'
(*
  (*! sharing Order.IntSyn = ThmSyn'.ModeSyn.IntSyn !*)
*)

module ThmSyn : Thmsyn.THMSYN
module ThmPrint : Thmprint.THMPRINT with module ThmSyn = ThmSyn
module Thm : THM with module ThmSyn = ThmSyn
