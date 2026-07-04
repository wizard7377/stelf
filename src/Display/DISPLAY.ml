module type DISPLAY = sig
  val register : (Info.t -> unit Lwt.t) -> unit
  val set_fallback_verbosity : Info.level -> unit
  val display' : Info.t -> unit

  val message :
    ?src:Info.src -> ?kind:Info.kind -> ?level:Info.level -> Info.form -> unit

  val chatter : ?src:Info.src -> ?kind:Info.kind -> int -> Info.form -> unit
  val chatter_s : ?src:Info.src -> ?kind:Info.kind -> int -> string -> unit

  val debug : ?src:Info.src -> ?level:Info.level -> Info.form -> unit
  val info : ?src:Info.src -> ?level:Info.level -> Info.form -> unit
  val warning : ?src:Info.src -> ?level:Info.level -> Info.form -> unit
  val error : ?src:Info.src -> ?level:Info.level -> Info.form -> unit
  val response : ?src:Info.src -> ?level:Info.level -> Info.form -> unit
end
