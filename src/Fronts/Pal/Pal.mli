val version : string
val logo : Display.form

module type PAL = PAL.PAL
module type PAL' = PAL.PAL'

module Reply = Reply
(** Structured results returned by the command pipeline. *)

module Render = Render
(** Renders {!Reply} values through the [Display] bus. *)

module Pal : PAL.PAL

module Opts : sig
  module Opts : OPTS.OPTS
end
