include module type of Modeprint_intf

module MakeModePrint (ModePrint__0 : sig
  (*! structure ModeSyn' : MODESYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = ModeSyn'.IntSyn !*)
  module Formatter : FORMATTER
  module Print : PRINT
end) : MODEPRINT
