include module type of ClausePrint_intf

module MakeClausePrint (ClausePrint__0 : sig
  (* Clause Printing *)
  (* Author: Frank Pfenning, Carsten Schuermann *)
  (* This is like printing of expressions, except that
   types are interpreted as programs and therefore
   printed with backward arrows `<-'
*)
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Formatter_param : FORMATTER

  (* PRINT inlined to avoid cycle with print_ *)
  module Print : sig
    module Formatter : FORMATTER

    val formatDec : IntSyn.dctx * IntSyn.dec -> Formatter.format
    val formatExp : IntSyn.dctx * IntSyn.exp -> Formatter.format
    val formatSpine : IntSyn.dctx * IntSyn.spine -> Formatter.format list
    val formatConDec : IntSyn.conDec -> Formatter.format
    val implicit : bool ref
  end

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Symbol : Symbol.SYMBOL
end) : CLAUSEPRINT
