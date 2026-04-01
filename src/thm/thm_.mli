include module type of Thm_intf

module Make_Thm (Thm__0 : sig
  module Global : GLOBAL
  module ThmSyn' : Thmsyn.THMSYN
  module TabledSyn : Tabledsyn.TABLEDSYN
  module ModeTable : Modetable.MODETABLE
  module Order : ORDER

  (*! sharing Order.IntSyn = ThmSyn'.ModeSyn.IntSyn !*)
  module ThmPrint : Thmprint.THMPRINT
end) : THM with module ThmSyn = Thm__0.ThmSyn'

module ThmSyn : Thmsyn.THMSYN
module ThmPrint : Thmprint.THMPRINT with module ThmSyn = ThmSyn
module Thm : THM with module ThmSyn = ThmSyn
