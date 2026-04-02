include module type of Init_intf

module Init (Init__0 : sig
  module MetaSyn' : Metasyn.METASYN
  module MetaAbstract : MetaAbstract_intf.METAABSTRACT with module MetaSyn = MetaSyn'
end) : INIT with module MetaSyn = Init__0.MetaSyn'
