module type SYNTAX = sig 
  module Common : Common.COMMON
  module type AST = Ast_intf.AST with module Common = Common
  module Ast : AST

  module type SGN = Sgn_intf.SGN with module Common = Common and module Ast = Ast
  module Sgn : SGN 
  module type MISC = Misc_intf.MISC with module Common = Common and module Ast = Ast
  module Misc : MISC 
end 
module Make_Syntax (Common : Common.COMMON) : SYNTAX with module Common = Common = struct
  module Common = Common
  module type AST = Ast_intf.AST with module Common = Common
  module Ast : AST = Ast.Make_Ast (Common)
  module type SGN = Sgn_intf.SGN with module Common = Common and module Ast = Ast
  module Sgn : SGN = Sgn.Make_Sgn (Common) (Ast)
  module type MISC = Misc_intf.MISC with module Common = Common and module Ast = Ast
  module Misc : MISC = Misc.Make_Misc (Common) (Ast)
end
module IntIdx : Common.CID with type t = int = struct 
  type t = int 
  let compare = compare 
  let equal = (=)
  let fresh = let c = ref 0 in fun () -> incr c; !c
  let pp fmt i = Format.fprintf fmt "%d" i
  let toString = string_of_int
  let show = toString
end

module type INTSYN = sig 
  
end
module IntSyn(Global : Global.Global_intf.GLOBAL) = Make_Syntax (struct 
  module Cid = IntIdx 
  module Mid = IntIdx
  module Tag = struct type t = Tag end
  module Global = Global
end) 

module ExtIdx : Common.CID with type t = string = struct 
  type t = string 
  let compare = compare 
  let equal = (=)
  let fresh = let c = ref 0 in fun () -> incr c; "ext" ^ string_of_int !c
  let pp fmt i = Format.fprintf fmt "%s" i
  let toString s = s
  let show = toString
end

module ExtSyn(Global : Global.Global_intf.GLOBAL) = Make_Syntax (struct 
  module Cid = ExtIdx 
  module Mid = ExtIdx
  module Tag = struct type t = Tag end
  module Global = Global
end)

module type EXTSYN = sig 
  module Global : Global.Global_intf.GLOBAL
  include (module type of ExtSyn(Global))
end