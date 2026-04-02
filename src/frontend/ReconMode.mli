include module type of ReconMode_intf

module ReconMode (ReconMode__0 : sig
  module Global : GLOBAL

  (*! structure ModeSyn' : MODESYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = ModeSyn'.IntSyn !*)
  (*! structure Paths' : PATHS !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = ModeSyn'.IntSyn !*)
  module ModePrint : Modeprint.MODEPRINT

  (*! sharing ModePrint.ModeSyn = ModeSyn' !*)
  module ModeDec : Modedec.MODEDEC
  module ReconTerm' : ReconTerm_intf.RECON_TERM
end) : RECON_MODE
