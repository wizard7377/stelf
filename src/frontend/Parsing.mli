include module type of Parsing_intf

module MakeParsing (Parsing__0 : sig
  module Stream' : STREAM
  module Lexer' : Lexer.LEXER
end) : PARSING

module Parsing : PARSING

include
  PARSING
    with module Stream = Parsing.Stream
     and module Lexer = Parsing.Lexer
