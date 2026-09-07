open! Timing
open! Global.Global_
open! Names.Names_
open! Print.Print_
include module type of FQUERY

module Fquery (Fquery__0 : sig
  module Global : GLOBAL
  module Names : NAMES
  module ReconQuery : RECONQUERY.RECON_QUERY
  module Timers : Timers.TIMERS
  module Print : PRINT
end) : FQUERY with module ExtQuery = Fquery__0.ReconQuery
