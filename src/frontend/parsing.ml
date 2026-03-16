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
  type nonrec 'a parser = lexResult Stream.front -> 'a * lexResult Stream.front

  (* recursive parser (allows parsing functions that need to parse
     a signature expression to temporarily suspend themselves) *)
  type 'a recParseResult =
    | Done of 'a
    | Continuation of 'a recParseResult parser

  type nonrec 'a recparser = 'a recParseResult parser

  (* useful combinator for recursive parsers *)
  val recwith : 'a recparser * ('a -> 'b) -> 'b recparser

  exception Error of string

  val error : Paths.region * string -> 'a
end

(* always raises Error *)
(* signature PARSING *)

(* # 1 "src/frontend/parsing.fun.ml" *)
open! Basis

module MakeParsing (Parsing__0 : sig
  module Stream' : STREAM
  module Lexer' : Lexer.LEXER
end) : PARSING = struct
  module Stream = Parsing__0.Stream'
  module Lexer = Parsing__0.Lexer'

  (*! structure Lexer = Lexer' !*)
  type nonrec lexResult = Lexer.token * Paths.region
  type nonrec 'a parser = lexResult Stream.front -> 'a * lexResult Stream.front

  type 'a recParseResult =
    | Done of 'a
    | Continuation of 'a recParseResult parser

  type nonrec 'a recparser = 'a recParseResult parser

  let rec recwith (recparser, func) f =
    begin match recparser f with
    | Done x, f' -> (Done (func x), f')
    | Continuation k, f' -> (Continuation (recwith (k, func)), f')
    end

  exception Error of string

  let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))
end

(*! structure Lexer' : LEXER !*)
(*! sharing Lexer'.Stream = Stream' !*)
(* functor Parsing *)
module Parsing = MakeParsing (struct
  module Stream' = Stream
  module Lexer' = Lexer.Lexer
end)
(*! structure Lexer' = Lexer !*)

(* # 1 "src/frontend/parsing.sml.ml" *)
