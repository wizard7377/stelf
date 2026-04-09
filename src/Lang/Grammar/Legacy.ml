
module Make_Legacy
    (I : Syntax.SYNTAX)
    (Lexer : Lexer.LEXER)
    (Parser : Parser.PARSER with module Lexer = Lexer) : GrammarSig.GRAMMAR =
struct
  module Lexer = Lexer
  module Parser = Parser
  module Syntax = I
  module Decl = struct
    type decl =
      | Dec of Syntax.Ast.dec
      | Define of string * Syntax.Ast.exp
      | Symbol of string * Syntax.Ast.exp
      | Fixity of string * Names.Names_.Fixity.fixity
      | Sort of string * Syntax.Ast.exp
      | Term of string * Syntax.Ast.exp
      | Rule of string * Syntax.Ast.exp
      | Prose of string
  end

  type state = { fixities : (string, Names.Names_.Fixity.fixity) Hashtbl.t }
  type 'a t = ('a, state) Parser.t

  let not_implemented what = Parser.err ("legacy parser not implemented: " ^ what)

  let name : string t = not_implemented "name"
  let exp : Syntax.Ast.exp t = not_implemented "exp"
  let typ : Syntax.Ast.exp t = not_implemented "typ"
  let dec : Syntax.Ast.dec t = not_implemented "dec"
  let full_dec : Syntax.Ast.dec t = not_implemented "full_dec"
  let doc : Decl.decl list t = not_implemented "doc"
end