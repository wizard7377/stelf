module type S = sig
  val use_color : bool
  val use_unicode : bool
  val verbosity : Display.Info.level
  val mute : bool
end

module type REPL = sig
  type response = Continue | Fail of string | Stop

  val stop : int -> unit
  (** Exit with a code *)

  val read : (string -> response Lwt.t) -> int Lwt.t

  val show : Format.formatter -> unit
  (** Show the REPL prompt. *)
end
