
module type RECON = sig
  include S.S
  module ReconThm : RECON_THM.RECON_THM
  module ReconTerm : RECON_TERM.RECON_TERM
  module ReconConDec : RECON_CONDEC.RECON_CONDEC
  module ReconMode : RECON_MODE.RECON_MODE
  module ReconModule : RECON_MODULE.RECON_MODULE
  module ReconQuery : RECON_QUERY.RECON_QUERY
end
