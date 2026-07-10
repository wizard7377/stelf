module type DISPLAY = sig
  val lock : Lwt_mutex.t
  val register : (Info.t -> unit Lwt.t) -> unit
  val set_fallback_verbosity : Info.level -> unit
  val display' : Info.t -> unit

  val message :
    ?src:Info.src -> ?kind:Info.kind -> ?level:Info.level -> Info.form -> unit

  val rich :
    ?src:Info.src -> ?kind:Info.kind -> ?level:Info.level -> Info.rich -> unit
  (** Emit pre-styled rich text. Terminal frontends render it with real
      colors/attributes; others flatten it to plain text. *)

  val chatter : ?src:Info.src -> ?kind:Info.kind -> int -> Info.form -> unit
  val chatter_s : ?src:Info.src -> ?kind:Info.kind -> int -> string -> unit
  val debug : ?src:Info.src -> ?level:Info.level -> Info.form -> unit
  val info : ?src:Info.src -> ?level:Info.level -> Info.form -> unit
  val warning : ?src:Info.src -> ?level:Info.level -> Info.form -> unit
  val error : ?src:Info.src -> ?level:Info.level -> Info.form -> unit
  val response : ?src:Info.src -> ?level:Info.level -> Info.form -> unit
end
