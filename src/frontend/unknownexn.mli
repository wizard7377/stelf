include module type of Unknownexn_intf

module MakeUnknownExn (UnknownExn__0 : sig
  val exnHistory : exn -> string list
end) : UNKNOWN_EXN
