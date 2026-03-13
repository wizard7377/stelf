open! Basis

module MakeParsing (Parsing__0 : sig
  module Stream' : STREAM
  module Lexer' : Lexer.LEXER
end) : PARSING = struct
  module Stream = Parsing__0.Stream'
  module Lexer = Parsing__0.Lexer'

  (*! structure Lexer = Lexer' !*)
  type nonrec lexResult = Lexer.token_ * Paths.region
  type nonrec 'a parser = lexResult Stream.front -> 'a * lexResult Stream.front

  type 'a recParseResult_ =
    | Done of 'a
    | Continuation of 'a recParseResult_ parser

  type nonrec 'a recparser = 'a recParseResult_ parser

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
