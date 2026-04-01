include module type of Recon_thm_intf

module ReconThm (ReconThm__0 : sig
  (* Reconstruct Termination Information *)
  (* Author: Carsten Schuermann *)
  (* Modified: Brigitte Pientka *)
  module Global : GLOBAL

  (* structure IntSyn : INTSYN *)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module Constraints : CONSTRAINTS
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  (*! structure Paths' : PATHS !*)
  module ThmSyn' : Thmsyn.THMSYN with module Names = Names
  module ReconTerm' : Recon_term.RECON_TERM

  (*! sharing ReconTerm'.IntSyn = IntSyn !*)
  (*! sharing ReconTerm'.Paths = Paths'  !*)
  module Print : PRINT
end) : RECON_THM with module ThmSyn = ReconThm__0.ThmSyn'
