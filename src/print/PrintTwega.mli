include module type of PrintTwega_intf

module MakePrintTwega
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Constraints : CONSTRAINTS)
    (Names : NAMES)
    (Formatter_param : FORMATTER) :
  PRINT_TWEGA
(*
  (* Printing *)
  (* Author: Frank Pfenning *)
  (* Modified: Jeff Polakow *)
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Formatter_param : FORMATTER
*)
