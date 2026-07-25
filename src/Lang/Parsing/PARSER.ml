(** The parsing library, which is used in the modern frontend as a system for
    parsing.
    @author Asher Frost *)

(** {2 The Parser Module}

    The original Twelf used a very complex stack based parser. Here, we use a
    more idiomatic (and, because of the simplicity of STELF not that
    theoretically slower) parser combinator library, which is based off
    Angstrom. *)

module type PARSER = sig
  include module type of Angstrom

  val with_fc : 'a t -> ('a * int * int) t
  val inside : string -> string -> 'a t -> 'a t
  val whitespace : unit t

  val blank : unit t
  (** Parse some non ["\n"] whitespace, then [whitespace] *)

  val ident : string t
  val ident1 : string t
  val keyword : string -> unit t
  val keywords : string list -> unit t
  val token : string -> unit t
  val string_lit : unit -> string t
  val given : bool -> 'a t -> 'a t
  val extend : 'a t -> bool * 'a t -> 'a t
  val ( let| ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( and| ) : 'a t -> 'b t -> ('a * 'b) t
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
  val ( and* ) : 'a t -> 'b t -> ('a * 'b) t
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
  val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t
  val ( let@ ) : 'a t -> ('a * int * int -> 'b t) -> 'b t
  val forget : 'a t -> unit t
end
