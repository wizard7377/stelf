include module type of Funprint_intf

module FunPrint (FunPrint__0 : sig
  (*! structure FunSyn' : FUNSYN !*)
  module Formatter : FORMATTER
  module Names : NAMES

  (*! sharing Names.IntSyn = FunSyn'.IntSyn !*)
  module Print : PRINT
end) : Funprint_intf.FUNPRINT
