
module Make_Grammar (IntSyn : Syntax.SYNTAX) (Lexer : Lexer.LEXER) (Parser : Parser.PARSER with module Lexer = Lexer) = struct 
  module Legacy = Legacy.Make_Legacy(IntSyn)(Lexer)(Parser)
  module Modern = Modern.Make_Modern(IntSyn)(Lexer)(Parser)

end