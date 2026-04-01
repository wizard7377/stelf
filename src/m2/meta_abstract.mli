include module type of Meta_abstract_intf

module MetaAbstract (MetaAbstract__0 : sig
  module Global : GLOBAL
  module MetaSyn : Metasyn.METASYN
  module MetaGlobal : Meta_global.METAGLOBAL
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = MetaSyn'.IntSyn !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing Modes.Modesyn.ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = MetaSyn'.IntSyn !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = MetaSyn'.IntSyn !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE
end) : METAABSTRACT with module MetaSyn = MetaAbstract__0.MetaSyn
