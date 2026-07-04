module type ERROR = sig
  type stage = Lex | Parse | Check | Total | Recon | Unknown | Other of string

  exception Err of stage * (Format.formatter -> unit)

  val err : ?stage:stage -> (Format.formatter -> unit) -> 'a
end
