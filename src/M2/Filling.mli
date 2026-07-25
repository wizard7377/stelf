include module type of FILLING

module Filling (Filling__0 : sig
  module MetaSyn' : Metasyn.METASYN
  module MetaAbstract : METAABSTRACT.METAABSTRACT with module MetaSyn = MetaSyn'
  module Search : Search.OLDSEARCH with module MetaSyn = MetaSyn'
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
  module Print : PRINT
end) : FILLING with module MetaSyn = Filling__0.MetaSyn'
