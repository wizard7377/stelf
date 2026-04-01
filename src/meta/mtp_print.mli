include module type of Mtp_print_intf

module MTPrint (MTPrint__0 : sig
  (* Meta Printer Version 1.3 *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module StateSyn' : Statesyn_intf.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn !*)
  (*! sharing StateSyn'.IntSyn = IntSyn !*)
  module Formatter' : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module FunPrint : Funprint_intf.FUNPRINT
end) : Mtp_print_intf.MTPRINT
