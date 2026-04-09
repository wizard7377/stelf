module Traits (Common : Common.COMMON)(Syntax : Syntax.SYNTAX) = struct
  open Common

  exception ParseError of Tag.Pos.range * string 

   class virtual parse =
    object
      method virtual parse_expression : string -> Syntax.Ast.exp
    end
end
  