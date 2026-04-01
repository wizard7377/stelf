include module type of Recon_term_intf

module ReconTerm (ReconTerm__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  (*! structure Paths' : PATHS !*)
  module Approx : APPROX

  (*! sharing Approx.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  (*! structure Cs_manager : CS_MANAGER !*)
  (*! sharing Cs_manager.IntSyn = IntSyn' !*)
  module StringTree : TABLE with type key = string
  module Msg : MSG
end) : RECON_TERM
