include module type of Subtree_intf

module SubTree (SubTree__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*!structure CompSyn' : COMPSYN !*)
  (*!  sharing CompSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*!  sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*!  sharing Unify.IntSyn = IntSyn'!*)
  module Print : PRINT

  (*!  sharing Print.IntSyn = IntSyn' !*)
  (* CPrint currently unused *)
  module CPrint : Cprint.CPRINT

  (*!  sharing CPrint.IntSyn = IntSyn' !*)
  (*!  sharing CPrint.CompSyn = CompSyn' !*)
  (* unused *)
  module Formatter : FORMATTER

  (*!  sharing Print.Formatter = Formatter !*)
  (* unused *)
  module Names : NAMES

  (*!  sharing Names.IntSyn = IntSyn' !*)
  module CsManager : CsManager.CS_MANAGER
end) : SUBTREE
