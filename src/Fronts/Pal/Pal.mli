val logo : Display.form
(** The STELF banner. Coloured only when [Display.set_color true] has been
    called by the frontend that owns the formatter. *)

module type PAL = PAL.PAL
module type PAL' = PAL.PAL'

module Reply = Reply
(** Structured results returned by the command pipeline. *)

module Render = Render
(** Renders {!Reply} values through the [Display] bus. *)

module Help = Help
(** The catalogue of [%]-commands and the overview [%help] prints. Exposed so
    that a command line consumer can answer from the same list the REPL does. *)

module Pal : PAL.PAL

module Opts : sig
  module Opts : OPTS.OPTS
end
