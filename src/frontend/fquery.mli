include module type of Fquery_intf

module Fquery (Fquery__0 : sig
  module Global : GLOBAL
  module Names : NAMES
  module ReconQuery : Recon_query.RECON_QUERY
  module Timers : Timers.TIMERS
  module Print : PRINT
end) : FQUERY with module ExtQuery = Fquery__0.ReconQuery
