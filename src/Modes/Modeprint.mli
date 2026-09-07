open! Formatter__Formatter_
open! Print.Print_
open! Names.Names_
include module type of MODEPRINT

module MakeModePrint (Names : NAMES) (Formatter : FORMATTER) (Print : PRINT) :
  MODEPRINT
