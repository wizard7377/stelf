module type GRAMMAR = sig 
  module Lexer : Lexer.LEXER
  module IntSyn : Lambda.Intsyn.INTSYN 
  module Parser : Parser.PARSER with module Lexer = Lexer
  type t 
  val parse : t Parser.t  
end  

