include module type of Qed_intf

module Qed (Qed__0 : sig
  module Global : GLOBAL
  module MetaSyn' : Metasyn.METASYN
end) : QED with module MetaSyn = Qed__0.MetaSyn'
