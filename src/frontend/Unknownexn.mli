include module type of Unknownexn_intf

module MakeUnknownExn (UnknownExn : sig
  val exnHistory : exn -> string list
end) : UNKNOWN_EXN
