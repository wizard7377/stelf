
(** {1 STELF Parser Combinators}

    This signature describes the reusable parser layer for STELF syntax. The
    concrete grammar will live in [Grammar]; this module only provides parser
    state, error handling, and combinators. *)

module type PARSER = sig
  module Lexer : Lexer.LEXER

  type +'a t
  type error = string
  type warning = string
  type info = { warnings : (warning * Lexer.pos) list }
  type 'a parse = Success of ('a * info) | ParseError of (error * Lexer.pos)

  (** Execute a parser on the given lexer buffer. *)
  val run : 'a t -> Lexer.lexbuf -> 'a parse * Lexer.lexbuf

  (** Lift a lexer computation into the parser layer. *)
  val lex : 'a Lexer.t -> 'a t

  (** Record a warning at the current position. *)
  val warn : warning -> unit t

  (** Fail with an error at the current position. *)
  val err : error -> 'a t

  (** Map a function over a parser result. *)
  val map : ('a -> 'b) -> 'a t -> 'b t

  (** Sequence two parsers, feeding the first result into the second. *)
  val bind : 'a t -> ('a -> 'b t) -> 'b t

  (** Return a successful parser without consuming input. *)
  val pure : 'a -> 'a t

  (** Monadic bind operator. *)
  val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t

  (** Monadic map operator. *)
  val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

  (** Combine two parsers and return both results. *)
  val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t

  (** Combine two parsers and return both results. *)
  val ( and* ) : 'a t -> 'b t -> ('a * 'b) t

  (** Sequence a parser and a continuation. *)
  val seq : 'a t -> ('a -> 'b t) -> 'b t

  (** Run one parser and discard its value. *)
  val seq_ : 'a t -> 'b t -> 'b t

  (** Try parsers in order until one succeeds. *)
  val alt : 'a t list -> 'a t

  (** Try a prefix parser and then a payload parser for each branch. *)
  val alt_ : (unit t * 'a t) list -> 'a t

  (** Parse zero or more occurrences. *)
  val many : 'a t -> 'a list t

  (** Parse one or more occurrences. *)
  val many1 : 'a t -> 'a list t

  (** Parse an optional value. *)
  val opt : 'a t -> 'a option t

  (** Parse items separated by a delimiter. *)
  val sep_by : 'a t -> 'b t -> 'a list t

  (** Parse one or more items separated by a delimiter. *)
  val sep_by1 : 'a t -> 'b t -> 'a list t

  (** Parse between two delimiters. *)
  val between : unit t -> 'a t -> unit t -> 'a t

  (** Consume a token and discard its value. *)
  val token : 'a t -> unit t

  val keyword : string -> unit t

  module Monad : sig
    (** Map a function over a parser result. *)
    val map : ('a -> 'b) -> 'a t -> 'b t

    (** Sequence two parser computations. *)
    val bind : 'a t -> ('a -> 'b t) -> 'b t

    (** Monadic bind operator. *)
    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t

    (** Monadic map operator. *)
    val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

    (** Pair the results of two parser computations. *)
    val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t

    (** Pair the results of two parser computations. *)
    val ( and* ) : 'a t -> 'b t -> ('a * 'b) t
    val ( << ) : 'a t -> 'b t -> 'a t
    val ( >> ) : 'a t -> 'b t -> 'b t

    (** Return a pure parser computation. *)
    val pure : 'a -> 'a t
  end
end

module type S = sig
  include PARSER
end



