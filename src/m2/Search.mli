include module type of Search_intf

module OLDSearch (OLDSearch__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module MetaGlobal : MetaGlobal_intf.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN

  (*! sharing MetaSyn'.IntSyn = IntSyn' !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  (*
                structure Assign : ASSIGN
                sharing Assign.IntSyn = IntSyn'
                *)
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
end) : OLDSEARCH with module MetaSyn = OLDSearch__0.MetaSyn'
