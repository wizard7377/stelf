(** {1 STELF Lexing Primitives}

    This module provides the small lexer core used by the STELF-specific
    parser layer. A lexer value is a stateful computation over a [lexbuf]; the
    buffer itself stays simple so grammar-specific logic can live higher up. *)

type source = Interactive | File of Fpath.t [@@deriving show, eq, ord]

(** Source position in the input buffer. *)
type pos = { source : source; line : int; column : int } [@@deriving show, eq, ord]

type range = pos * pos [@@deriving show, eq, ord]


let make_range (start_pos : pos) (end_pos : pos) : range =
  assert (start_pos.source = end_pos.source);
  start_pos, end_pos
  
(** The current lexer buffer and position state. *)
type lexbuf = {
  buffer : string;
  source : source;
  current_offset : int;
  current_source : source;
}
[@@deriving show]
 