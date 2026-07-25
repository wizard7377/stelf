include module type of PRINT

module MakePrint
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Constraints : CONSTRAINTS)
    (Names : NAMES)
    (Formatter_param : FORMATTER)
    (Symbol : Symbol.SYMBOL) : PRINT
(*
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
*)

module Print : PRINT
include PRINT
module ClausePrint : CLAUSEPRINT.CLAUSEPRINT
module PrintTeX : PRINT
module ClausePrintTeX : CLAUSEPRINT.CLAUSEPRINT
