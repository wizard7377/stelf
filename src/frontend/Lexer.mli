include module type of Lexer_intf

module MakeLexer (Stream : STREAM) : LEXER

module Lexer : LEXER

include LEXER with module Stream = Lexer.Stream
