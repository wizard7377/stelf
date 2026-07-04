module type ERROR = ERROR.ERROR

module Error : ERROR = struct
  type stage = Lex | Parse | Check | Total | Recon | Unknown | Other of string

  exception Err of stage * (Format.formatter -> unit)

  let err ?(stage = Unknown) form = raise (Err (stage, form))
end

let () = Printexc.register_printer (function Error.Err (_, form) -> Some (Format.asprintf "%t" form) | _ -> None)
