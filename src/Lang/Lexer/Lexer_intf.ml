(** {1 STELF Lexing Primitives}

    This module provides the small lexer core used by the STELF-specific
    parser layer. A lexer value is a stateful computation over a [lexbuf]; the
    buffer itself stays simple so grammar-specific logic can live higher up. *)

type source = Interactive | File of Fpath.t [@@deriving show, eq, ord]

(** Source position in the input buffer. *)
type pos = { source : source; line : int; column : int } [@@deriving show, eq, ord]

(** The current lexer buffer and position state. *)
type lexbuf = {
  buffer : string;
  source : source;
  current_offset : int;
  current_source : source;
}
[@@deriving show]

module type LEXER = sig
  type nonrec source = source
  type nonrec pos = pos
  type nonrec lexbuf = lexbuf
  type +'a t

  (** Build an initial lexer buffer from a string. *)
  val of_string : ?source:source -> string -> lexbuf

  (** Lift a raw state transition into the lexer monad. *)
  val take : (lexbuf -> (lexbuf * 'a) option) -> 'a t

  (** Expose the underlying state transition for a lexer computation. *)
  val run : 'a t -> lexbuf -> (lexbuf * 'a) option

  (** Read the current source position. *)
  val get_pos : lexbuf -> pos

  (** Read the current source tag. *)
  val get_source : lexbuf -> source

  (** Read the current byte offset. *)
  val get_offset : lexbuf -> int

  (** Repeat a lexer computation until it fails, collecting results. *)
  val repeat : 'a t -> 'a list t

  (** Consume exactly [n] characters. *)
  val exact : int -> string t

  (** Consume input until the predicate matches. *)
  val until : (char -> bool) -> string t

  (** Consume one or more whitespace characters. *)
  val space1 : string t

  (** Consume one or more non-whitespace characters. *)
  val symbol1 : string t

  (** Check whether the next characters match a keyword. *)
  val keyword : string -> bool t

  module Monad : sig
    (** Map a function over a lexer computation. *)
    val map : ('a -> 'b) -> 'a t -> 'b t

    (** Sequence two lexer computations. *)
    val bind : 'a t -> ('a -> 'b t) -> 'b t

    (** Monadic bind operator. *)
    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t

    (** Monadic map operator. *)
    val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

    (** Pair the results of two lexer computations. *)
    val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t

    (** Pair the results of two lexer computations. *)
    val ( and* ) : 'a t -> 'b t -> ('a * 'b) t

    (** Return a pure lexer computation. *)
    val pure : 'a -> 'a t

    (** Capture the current lexer state as a value. *)
    val state : lexbuf t
  end
end
