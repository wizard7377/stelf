include module type of Parsing_intf

module MakeParsing (Stream : STREAM) (Lexer : Lexer.LEXER) : PARSING

module Parsing : PARSING

include
  PARSING
    with module Stream = Parsing.Stream
     and module Lexer = Parsing.Lexer
