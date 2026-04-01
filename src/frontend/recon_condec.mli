include module type of Recon_condec_intf

module ReconConDec (ReconConDec__0 : sig
  (* Reconstruct signature entries *)
  (* Author: Frank Pfenning *)
  (* Modified: Roberto Virga, Jeff Polakow *)
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  (*! structure Paths' : PATHS !*)
  module ReconTerm' : Recon_term.RECON_TERM

  (*! sharing ReconTerm'.IntSyn = IntSyn' !*)
  (*! sharing ReconTerm'.Paths = Paths' !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module Strict : STRICT

  (*! sharing Strict.IntSyn = IntSyn' !*)
  (*! sharing Strict.Paths = Paths' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Timers : Timers.TIMERS
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Msg : MSG
end) : RECON_CONDEC
