include module type of Recon_query_intf

module ReconQuery (ReconQuery__0 : sig
  (* Reconstruct queries *)
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
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Strict : STRICT

  (*! sharing Strict.IntSyn = IntSyn' !*)
  (*! sharing Strict.Paths = Paths' !*)
  module Timers : Timers.TIMERS
  module Print : PRINT
end) : RECON_QUERY
