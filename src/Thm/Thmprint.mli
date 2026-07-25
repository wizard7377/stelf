include module type of THMPRINT

module ThmPrint (ThmPrint__0 : sig
  module ThmSyn' : Thmsyn.THMSYN
  module Formatter : FORMATTER
end) : THMPRINT with module ThmSyn = ThmPrint__0.ThmSyn'
