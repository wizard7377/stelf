include module type of PrintOmdoc_intf

module MakePrintOMDoc
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Constraints : CONSTRAINTS)
    (Names : NAMES)
    (Formatter_param : FORMATTER) :
  PRINT_OMDOC
(*
  (* Printing *)
  (* Author: Frank Pfenning *)
  (* Modified: Jeff Polakow *)
  (* Modified: Carsten Schuermann *)
  (* Modified: Florian Rabe *)
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
