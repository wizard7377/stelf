val setup_log : level:Logs.level -> unit -> unit

module Level : sig
  type t = Debug | Info | Warning | Error
end

module Group : sig
  val approx : Logs.src
  val check : Logs.src
  val compile : Logs.src
  val typecheck : Logs.src
  val unify : Logs.src
  val cover : Logs.src
  val parse : Logs.src
  val reduce : Logs.src
  val meta : Logs.src
end

val msg :
  Logs.src -> Level.t -> (Format.formatter -> 'a -> unit) -> 'a -> unit

module Fmt : module type of Fmt
