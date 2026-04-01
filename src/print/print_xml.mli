include module type of Print_xml_intf

module MakePrintXML (PrintXML__0 : sig
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
end) : PRINT_XML
