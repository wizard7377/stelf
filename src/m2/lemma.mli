include module type of Lemma_intf

module Lemma (Lemma__0 : sig
  module MetaSyn' : Metasyn.METASYN
  module MetaAbstract : Meta_abstract.METAABSTRACT with module MetaSyn = MetaSyn'
end) : LEMMA with module MetaSyn = Lemma__0.MetaSyn'
