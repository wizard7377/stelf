include module type of PrintXml_intf

module MakePrintXML
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Constraints : CONSTRAINTS)
    (Names : NAMES)
    (Formatter_param : FORMATTER) :
  PRINT_XML
(*
  (* Printing *)
  (* Author: Frank Pfenning *)
  (* Modified: Jeff Polakow *)
  (* Modified: Carsten Schuermann *)
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
