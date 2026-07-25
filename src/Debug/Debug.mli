module Level : sig
  type t = Debug | Info | Warning | Error | App
end

module Group : sig
  val approx : Display.Info.src
  val check : Display.Info.src
  val compile : Display.Info.src
  val typecheck : Display.Info.src
  val unify : Display.Info.src
  val cover : Display.Info.src
  val parse : Display.Info.src
  val reduce : Display.Info.src
  val meta : Display.Info.src
  val pal : Display.Info.src
  val default : Display.Info.src
end

val msg' :
  ?src:Display.Info.src ->
  ?level:Level.t ->
  (Format.formatter -> 'a -> unit) ->
  'a ->
  unit

val msg : ?src:Display.Info.src -> ?level:Level.t -> unit Fmt.t -> unit

module Fmt : sig
  include module type of Fmt

  val exact : string -> 'a Fmt.t
  val shown : ('a -> string) -> 'a Fmt.t
  val shown_exact : ('a -> string) -> 'a -> 'b Fmt.t
end
