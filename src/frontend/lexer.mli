include module type of Lexer_intf

module MakeLexer (Lexer__0 : sig
  module Stream' : STREAM
end) : LEXER

module Lexer : LEXER

include LEXER with module Stream = Lexer.Stream
