include module type of Mtp_search_intf

module MTPSearch (MTPSearch__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module MTPGlobal : Mtp_global.MTPGLOBAL
  module StateSyn' : Statesyn_intf.STATESYN

  (*! sharing StateSyn'.FunSyn.IntSyn = IntSyn' !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn'              !*)
  module Assign : Assign.ASSIGN

  (*! sharing Assign.IntSyn = IntSyn'   !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module Compile : COMPILE

  (*! sharing Compile.IntSyn = IntSyn' !*)
  (*! sharing Compile.CompSyn = CompSyn' !*)
  module CPrint : Cprint.CPRINT

  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Names : NAMES
end) : Mtp_search_intf.MTPSEARCH
