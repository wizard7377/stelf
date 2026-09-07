include module type of LEMMA

module Lemma (Lemma__0 : sig
  module MetaSyn' : Metasyn.METASYN
  module MetaAbstract : METAABSTRACT.METAABSTRACT with module MetaSyn = MetaSyn'
end) : LEMMA with module MetaSyn = Lemma__0.MetaSyn'
