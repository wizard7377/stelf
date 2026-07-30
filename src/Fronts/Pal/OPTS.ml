module type OPTS = sig
  type 'a t = 'a Cmdliner.Arg.t

  (** When to emit ANSI styling.

      [Auto] defers to whatever terminal detection the frontend has already
      done -- isatty, [TERM] and [NO_COLOR] -- rather than assuming a terminal.
      The previous [bool] could not express that, which is why colour was
      unconditionally on and leaked escapes into redirected output. *)
  type color_when = Auto | Always | Never

  val verbosity : Display.Info.level t
  val mute : bool t
  val color : color_when t
  val unicode : bool t
  val file_list : string list t
  val help : string option t
end
