(* # 1 "src/frontend/parsing.sig.ml" *)
open! Basis

(* General basis for parsing modules *)
(* Author: Frank Pfenning *)

module type PARSING = sig
  module Stream : STREAM
  module Lexer : Lexer.LEXER

  (*
  structure Lexer : LEXER
    sharing Lexer.Stream = Stream
  *)
  type nonrec lexResult = Lexer.token * Paths.region
  type 'a parser = lexResult Stream.front -> 'a * lexResult Stream.front

  (* recursive parser (allows parsing functions that need to parse
     a signature expression to temporarily suspend themselves) *)
  type 'a recParseResult =
    | Done of 'a
    | Continuation of 'a recParseResult parser

  type 'a recparser = 'a recParseResult parser

  (* useful combinator for recursive parsers *)
  val recwith : 'a recparser * ('a -> 'b) -> 'b recparser

  exception Error of string

  val error : Paths.region * string -> 'a
end
