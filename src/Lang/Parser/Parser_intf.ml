
(** {1 STELF Parser Combinators}

    This signature describes the reusable parser layer for STELF syntax. The
    concrete grammar will live in [Grammar]; this module only provides parser
    state, error handling, and combinators. *)

(** Type of parser descriptions, which are used in error messages *)
type 'a description = 
  (* ? *)
  Unknown |
  (* empty token *)
  Empty | 
  (* <kind>: ... *) 
  Form of 'a * 'a description | 
  (* x, y, z *)
  Seq of 'a description list | 
  (* Lexeme *)
  Token of string | 
  (* End of file *)
  EOF | 
  (* List of ... *)
  List0 of 'a description | 
  (* Non-empty list of ... *)
  List1 of 'a description | 
  (* Alternative *)
  Alt of 'a description list | 
  (* Description *)
  Describe of 'a description * string

module type PARSER = sig 
  module Lexer : Lexer.LEXER

  type ('a, 'b) t
  type error = string
  type warning = string
  type node
  type info = { 
    warnings : (warning * Lexer.pos) list;

  }
  type ('a, 'b) parse = Success of 'a * 'b * info | ParseError of (error * Lexer.pos) list

  val commit : (unit, 'b) t

  val fc : (Tag.Pos.range -> 'a -> 'b) -> ('a, 'c) t -> ('b, 'c) t

  val note : node -> ('a, 'b) t -> ('a, 'b) t
  (* Execute a parser on the given lexer buffer. *)
  val run : ('a, 'b) t -> Lexer.lexbuf -> 'b -> ('a, 'b) parse * Lexer.lexbuf
  (* Run a parser against a string and return either a value or errors. *)
  val debug : ('a, 'b) t -> 'b -> string -> ('a, error list) result

  (* Lift a lexer computation into the parser layer. *)
  val lex : 'a Lexer.t -> ('a, 'b) t

  (** Record a warning at the current position. *) 
  val warn : warning -> (unit, 'b) t

  (** Fail with an error at the current position. *)
  val err : error -> ('a, 'b) t

  (** Map a function over a parser result. *)
  val map : ('a -> 'b) -> ('a, 'c) t -> ('b, 'c) t

  (** Sequence two parsers, feeding the first result into the second. *)
  val bind : ('a, 'c) t -> ('a -> ('b, 'c) t) -> ('b, 'c) t

  (** Return a successful parser without consuming input. *)
  val pure : 'a -> ('a, 'b) t

  (** Monadic bind operator. *)
  val ( let* ) : ('a, 'b) t -> ('a -> ('c, 'b) t) -> ('c, 'b) t

  (** Monadic map operator. *)
  val ( let+ ) : ('a, 'b) t -> ('a -> 'c) -> ('c, 'b) t

  (** Combine two parsers and return both results. *)
  val ( and+ ) : ('a, 'b) t -> ('c, 'b) t -> ('a * 'c, 'b) t

  (** Combine two parsers and return both results. *)
  val ( and* ) : ('a, 'b) t -> ('c, 'b) t -> ('a * 'c, 'b) t

  (** Sequence a parser and a continuation. *)
  val seq : ('a, 'b) t -> ('a -> ('c, 'b) t) -> ('c, 'b) t

  (** Run one parser and discard its value. *)
  val seq_ : ('a, 'b) t -> ('c, 'b) t -> ('c, 'b) t

  (** Try parsers in order until one succeeds. *)
  val alt : ('a, 'b) t list -> ('a, 'b) t

  (** Try a prefix parser and then a payload parser for each branch. *)
  val alt_ : ((unit, 'c) t * ('a, 'c) t) list -> ('a, 'c) t 

  (** Parse zero or more occurrences. *)
  val many : ('a, 'c) t -> ('a list, 'c) t

  (** Parse one or more occurrences. *)
  val many1 : ('a, 'c) t -> ('a list, 'c) t

  (** Parse an optional value. *)
  val opt : ('a, 'c) t -> ('a option, 'c) t

  (** Parse items separated by a delimiter. *)
  val sep_by : ('a, 'c) t -> ('b, 'c) t -> ('a list, 'c) t

  (** Parse one or more items separated by a delimiter. *)
  val sep_by1 : ('a, 'c) t -> ('b, 'c) t -> ('a list, 'c) t

  (** Parse between two delimiters. *)
  val between : (unit, 'c) t -> ('a, 'c) t -> (unit, 'c) t -> ('a, 'c) t

  (** Consume a token and discard its value. *)
  val token : ('a, 'c) t -> (unit, 'c) t

  val keyword : string -> (unit, 'c) t

  module Monad : sig
    (** Map a function over a parser result. *)
    val map : ('a -> 'b) -> ('a, 'c) t -> ('b, 'c) t

    (** Sequence two parser computations. *)
    val bind : ('a, 'c) t -> ('a -> ('b, 'c) t) -> ('b, 'c) t

    (** Monadic bind operator. *)
    val ( let* ) : ('a, 'c) t -> ('a -> ('b, 'c) t) -> ('b, 'c) t

    (** Monadic map operator. *)
    val ( let+ ) : ('a, 'c) t -> ('a -> 'b) -> ('b, 'c) t

    (** Pair the results of two parser computations. *)
    val ( and+ ) : ('a, 'c) t -> ('b, 'c) t -> ('a * 'b, 'c) t

    (** Pair the results of two parser computations. *)
    val ( and* ) : ('a, 'c) t -> ('b, 'c) t -> ('a * 'b, 'c) t
    val ( << ) : ('a, 'c) t -> ('b, 'c) t -> ('a, 'c) t
    val ( >> ) : ('a, 'c) t -> ('b, 'c) t -> ('b, 'c) t

    (** Return a pure parser computation. *)
    val pure : 'a -> ('a, 'c) t

    val get_state : ('c, 'c) t
    val set_state : 'c -> (unit, 'c) t

    val fix : (('a, 'c) t -> ('a, 'c) t) -> ('a, 'c) t
  end
end

module type S = sig
  include PARSER
end



