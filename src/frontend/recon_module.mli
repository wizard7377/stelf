include module type of Recon_module_intf

module ReconModule (ReconModule__0 : sig
  (* Elaboration for module expressions *)
  (* Author: Kevin Watkins *)
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  (*! structure Paths' : PATHS !*)
  module ReconTerm' : Recon_term.RECON_TERM

  (*! sharing ReconTerm'.IntSyn = IntSyn !*)
  (*! sharing ReconTerm'.Paths = Paths' !*)
  module ModSyn' : Modsyn.MODSYN with module Names = Names

  (*! sharing ModSyn'.IntSyn = IntSyn !*)
  module IntTree : TABLE with type key = IntSyn.cid
end) : RECON_MODULE with module ModSyn = ReconModule__0.ModSyn'
