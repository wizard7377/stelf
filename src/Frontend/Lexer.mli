include module type of LEXER
module MakeLexer (Stream : STREAM) : LEXER
module Lexer : LEXER
include LEXER with module Stream = Lexer.Stream
