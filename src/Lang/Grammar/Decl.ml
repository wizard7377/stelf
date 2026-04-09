module type DECL = sig 
  module C : Syntax__Common.COMMON 
  module I : Syntax.SYNTAX with module Common = C 
  
  type decl = 
    | Dec of I.Ast.dec 
    | Define of string * I.Ast.exp
    | Symbol of string * I.Ast.exp
    | Fixity of string * Names.Names_.Fixity.fixity
    | Sort of string * I.Ast.exp
    | Term of string * I.Ast.exp
    | Rule of string * I.Ast.exp
    | Prose of string
end 
    
module Make_Decl (C : Syntax__Common.COMMON) (I : Syntax.SYNTAX with module Common = C) : DECL with module C = C and module I = I = struct 
  module C = C 
  module I = I 
  
  type decl = 
    | Dec of I.Ast.dec 
    | Define of string * I.Ast.exp
    | Symbol of string * I.Ast.exp
    | Fixity of string * Names.Names_.Fixity.fixity
    | Sort of string * I.Ast.exp
    | Term of string * I.Ast.exp
    | Rule of string * I.Ast.exp
    | Prose of string

end