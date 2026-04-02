include module type of Tomegaprint_intf

module TomegaPrint (TomegaPrint__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  (*   structure Normalize : NORMALIZE *)
  (*! sharing Normalize.IntSyn = IntSyn' !*)
  (*! sharing Normalize.Tomega = Tomega' !*)
  module Formatter : FORMATTER
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Print : PRINT with module Formatter = Formatter
end) : TOMEGAPRINT
