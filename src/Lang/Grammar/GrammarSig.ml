module type GRAMMAR = sig 
  module Lexer : Lexer.LEXER
  module Syntax : Syntax.SYNTAX
  module Parser : Parser.PARSER with module Lexer = Lexer
  module Decl : sig
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
  
  type state = {
    fixities : (string, Names.Names_.Fixity.fixity) Hashtbl.t
  }
  type 'a t = ('a, state) Parser.t
  
  val exp : Syntax.Ast.exp t
  val typ : Syntax.Ast.exp t
  val dec : Syntax.Ast.dec t
  val full_dec : Syntax.Ast.dec t
  val name : string t 
  val doc : Decl.decl list t
end  

     