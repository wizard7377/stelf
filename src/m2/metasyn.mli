include module type of Metasyn_intf

module Make_MetaSyn (MetaSyn__0 : sig
  module Whnf : WHNF
end) : METASYN
