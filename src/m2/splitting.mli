include module type of Splitting_intf

module Splitting (Splitting__0 : sig
  module Global : GLOBAL
  module MetaSyn' : Metasyn.METASYN
  module MetaAbstract : Meta_abstract.METAABSTRACT with module MetaSyn = MetaSyn'
  module MetaPrint : Meta_print.METAPRINT with module MetaSyn = MetaSyn'
  module ModeTable : Modetable.MODETABLE

  (*! sharing Modes.Modesyn.ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = MetaSyn'.IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
  module Unify : UNIFY
end) : Splitting_intf.SPLITTING with module MetaSyn = Splitting__0.MetaSyn'
