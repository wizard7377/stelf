include module type of Print_intf

module MakePrint (Print__0 : sig
  (* Printing *)
  (* Author: Frank Pfenning *)
  (* Modified: Jeff Polakow, Roberto Virga *)
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
  module Symbol : Symbol.SYMBOL
end) : PRINT

module Print : PRINT
include PRINT
module ClausePrint : ClausePrint_intf.CLAUSEPRINT
module PrintTeX : PRINT
module ClausePrintTeX : ClausePrint_intf.CLAUSEPRINT
