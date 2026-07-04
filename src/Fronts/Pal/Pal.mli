val version : string
val logo : Display.form

module type PAL = PAL.PAL
module type PAL' = PAL.PAL'

module Pal : PAL.PAL
module Opts : sig
  module Opts : OPTS.OPTS
end
