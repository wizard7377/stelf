include module type of FUNPRINT

module FunPrint (FunPrint__0 : sig
  (*! structure FunSyn' : FUNSYN !*)
  module Formatter : FORMATTER
  module Names : NAMES

  (*! sharing Names.IntSyn = FunSyn'.IntSyn !*)
  module Print : PRINT
end) : FUNPRINT.FUNPRINT
