include module type of UNKNOWNEXN

module MakeUnknownExn (UnknownExn : sig
  val exnHistory : exn -> string list
end) : UNKNOWN_EXN
