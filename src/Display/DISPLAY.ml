module type DISPLAY = sig
  val register : (Info.t -> unit Lwt.t) -> unit
  val display' : Info.t -> unit

  val message :
    ?src:Info.src -> ?kind:Info.kind -> ?level:Info.level -> Form.Form.t -> unit

  val chatter : ?src:Info.src -> ?kind:Info.kind -> int -> Form.Form.t -> unit
  val chatter_s : ?src:Info.src -> ?kind:Info.kind -> int -> string -> unit

  val debug : ?src:Info.src -> ?level:Info.level -> Form.Form.t -> unit
  val info : ?src:Info.src -> ?level:Info.level -> Form.Form.t -> unit
  val warning : ?src:Info.src -> ?level:Info.level -> Form.Form.t -> unit
  val error : ?src:Info.src -> ?level:Info.level -> Form.Form.t -> unit
end

module Form = Form.Form
