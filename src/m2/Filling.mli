include module type of Filling_intf

module Filling (Filling__0 : sig
  module MetaSyn' : Metasyn.METASYN
  module MetaAbstract : MetaAbstract_intf.METAABSTRACT with module MetaSyn = MetaSyn'
  module Search : Search.OLDSEARCH with module MetaSyn = MetaSyn'
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
  module Print : PRINT
end) : FILLING with module MetaSyn = Filling__0.MetaSyn'
