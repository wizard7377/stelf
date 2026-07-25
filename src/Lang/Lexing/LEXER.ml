open Tag.Pos

module type LEXER = sig
  type nonrec source = source
  type nonrec pos = pos
  type nonrec lexbuf = lexbuf
  type +'a t

  val of_string : ?source:source -> string -> lexbuf
  (** Build an initial lexer buffer from a string. *)

  val take : (lexbuf -> (lexbuf * 'a) option) -> 'a t
  (** Lift a raw state transition into the lexer monad. *)

  val run : 'a t -> lexbuf -> (lexbuf * 'a) option
  (** Expose the underlying state transition for a lexer computation. *)

  val get_pos : lexbuf -> pos
  (** Read the current source position. *)

  val get_source : lexbuf -> source
  (** Read the current source tag. *)

  val get_offset : lexbuf -> int
  (** Read the current byte offset. *)

  val repeat : 'a t -> 'a list t
  (** Repeat a lexer computation until it fails, collecting results. *)

  val exact : int -> string t
  (** Consume exactly [n] characters. *)

  val until : (char -> bool) -> string t
  (** Consume input until the predicate matches. *)

  val space1 : string t
  (** Consume one or more whitespace characters. *)

  val symbol1 : string t
  (** Consume one or more non-whitespace characters. *)

  val keyword : string -> bool t
  (** Check whether the next characters match a keyword. *)

  val lower_ident : (string list * string) t
  (** Lex exactly one non-reserved, regular symbol: 
  This works as follows
  {ol
    {- If the first charecter is {v _ v}, it fails -}
    {- If any charecter is {v % v}, {v { v} {v } v}, {v ( v} {v ) v}, {v [ v} {v ] v} and is not directly precceeded by the chareceter {v % v}, it fails -}
    {- Stops at whitespace -}
  }
    Then, we return whatever is left

    @return a tuple of the form (namespace, name) where namespace is a list of strings representing the namespace path and name is the final identifier. For example, if the input is "Foo.Bar.baz", we would return (["Foo"; "Bar"], "baz").
  *)

  val upper_ident : (string list * string) t
  (** Just like {!lower_ident}, except {e must e} start with {v _ v} (the term uppercase is maintained from Twelf, despite the fact that charecter case is now irrelevant) *)

  val op_ident : (string list * string) t
  (** Lex a symbolic identifier *)

  val any_ident : (string list * string) t

  module Monad : sig
    val map : ('a -> 'b) -> 'a t -> 'b t
    (** Map a function over a lexer computation. *)

    val bind : 'a t -> ('a -> 'b t) -> 'b t
    (** Sequence two lexer computations. *)

    val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
    (** Monadic bind operator. *)

    val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t
    (** Monadic map operator. *)

    val ( and+ ) : 'a t -> 'b t -> ('a * 'b) t
    (** Pair the results of two lexer computations. *)

    val ( and* ) : 'a t -> 'b t -> ('a * 'b) t
    (** Pair the results of two lexer computations. *)

    val pure : 'a -> 'a t
    (** Return a pure lexer computation. *)

    val state : lexbuf t
    (** Capture the current lexer state as a value. *)

    val ( >> ) : 'a t -> 'b t -> 'b t
    val ( << ) : 'a t -> 'b t -> 'a t
  end
end
