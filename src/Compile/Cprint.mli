open! Names.Names_
open! Print.Print_
open! Formatter__Formatter_
include module type of CPRINT

module Make_CPrint (Print_ : PRINT) (Formatter_ : FORMATTER) (Names_ : NAMES) :
  CPRINT
