(* TODO: Thinks that will be added eventually 
Groups (sections, list, etc)
Math markup 
Boxes*)

(** Common colors for the foreground and background (for use with {!FORM}) *)
module type COLORS = sig
  type t

  val black : t
  val red : t
  val green : t
  val yellow : t
  val blue : t
  val magenta : t
  val cyan : t
  val white : t
  val orange : t
  val rgb : int -> int -> int -> t
end

module type FORM = sig
  type t
  type style = t -> t
  type 'a scribe = 'a -> t

  module Style : sig
    val bold : style
    val italic : style
    val underline : style

    module Fore : COLORS with type t := style
    module Back : COLORS with type t := style
  end

  module Syntax : sig 
    val syntax : style 
  end

  val ( +++ ) : t -> t -> t
  val ( ++ ) : t -> t -> t
  val style : style -> t -> t
  val styles : style list -> t -> t
  val empty : t
  val concat : ?sep:t -> t list -> t
  val string : string -> t
  val int : int -> t
  val char : char -> t
  val bool : bool -> t
  val non_breaking_space : ?n:int -> unit -> t
  val space : ?n:int -> unit -> t
  val shown : ('a -> string) -> 'a -> t
  val inside : t * t -> t -> t
  val nl : ?n:int -> unit -> t
  val each : ?sep:t -> ('a -> t) -> 'a list -> t
  val hbox : t list -> t
  val vbox : t list -> t
  val hvbox : t list -> t
  val markup : t -> Notty.image
  val shown_many : ?sep:t -> ('a -> string) -> 'a list -> t
  val optional : ?def:t -> ('a -> t) -> 'a option -> t
  val to_plain : t -> string
  val fmt : t Fmt.t
  val header : level:int -> t -> t
  val show : t -> Notty.image
  val custom : unit Fmt.t -> t
end
