include module type of Recursion_intf

module Recursion (Recursion__0 : sig
  module Global : GLOBAL
  module MetaGlobal : MetaGlobal_intf.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = MetaSyn'.IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = MetaSyn'.IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
  module Order : ORDER

  (*! sharing Order.IntSyn = MetaSyn'.IntSyn !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing Modes.Modesyn.ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
  module Lemma : Lemma_intf.LEMMA with module MetaSyn = MetaSyn'
  module Filling : Filling_intf.FILLING with module MetaSyn = MetaSyn'
  module MetaPrint : MetaPrint_intf.METAPRINT with module MetaSyn = MetaSyn'
  module MetaAbstract : MetaAbstract_intf.METAABSTRACT with module MetaSyn = MetaSyn'
  module Formatter : FORMATTER
end) : Recursion_intf.RECURSION with module MetaSyn = Recursion__0.MetaSyn'
