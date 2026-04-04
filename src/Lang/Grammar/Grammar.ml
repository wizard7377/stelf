
module Make_Grammar (IntSyn : Lambda.Intsyn.INTSYN) (Lexer : Lexer.LEXER) (Parser : Parser.PARSER with module Lexer = Lexer) = struct 
  module rec Dec : GrammarSig.GRAMMAR with module Lexer = Lexer and module IntSyn = IntSyn and module Parser = Parser and type t = IntSyn.dec = GrammarDec.Make_Dec (Lexer) (Parser) (IntSyn) (Exp)
  and Exp : GrammarSig.GRAMMAR with module Lexer = Lexer and module IntSyn = IntSyn and module Parser = Parser and type t = IntSyn.exp = GrammarExp.Make_Exp (Lexer) (Parser) (IntSyn)
end
include Make_Grammar (Lambda.Intsyn.IntSyn) (Lexer.Lexer) (Parser.Make_Parser (Lexer.Lexer))      