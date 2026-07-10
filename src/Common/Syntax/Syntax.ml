module type SYNTAX = sig
  module Common : Common.COMMON

  module type AST = AST.AST with module Common = Common

  module Ast : AST

  module type SGN = SGN.SGN with module Common = Common and module Ast = Ast

  module Sgn : SGN

  module type MISC = MISC.MISC with module Common = Common and module Ast = Ast

  module Misc : MISC
end

module Make_Syntax (Common : Common.COMMON) :
  SYNTAX with module Common = Common = struct
  module Common = Common

  module type AST = AST.AST with module Common = Common

  module Ast : AST = Ast.Make_Ast (Common)

  module type SGN = SGN.SGN with module Common = Common and module Ast = Ast

  module Sgn : SGN = Sgn.Make_Sgn (Common) (Ast)

  module type MISC = MISC.MISC with module Common = Common and module Ast = Ast

  module Misc : MISC = Misc.Make_Misc (Common) (Ast)
end

(* Generative so that each instantiation has its OWN [counter]: constant ids
   ([Cid]) and structure/module ids ([Mid]) must be independent sequences.
   Sharing one counter (a plain [module Cid = IntIdx] alias) let structure ids
   run past [Global.maxMid] once many constants had been added, overflowing the
   fixed-size [componentsArray] in [Names] with a [Subscript]. *)
module IntIdx () : Common.CID with type t = int = struct
  type t = int

  let compare = compare
  let equal = ( = )
  let counter = ref 0

  let fresh () =
    incr counter;
    !counter

  let reset () = counter := 0
  let pp fmt i = Format.fprintf fmt "%d" i
  let toString = string_of_int
  let show = toString
end

module type INTSYN = sig end

module IntSyn (Global : Global.GLOBAL.GLOBAL) = Make_Syntax (struct
  module Cid = IntIdx ()
  module Mid = IntIdx ()

  module Tag = struct
    type t = Tag
  end

  module Global = Global
end)

module ExtIdx () : Common.CID with type t = string = struct
  type t = string

  let compare = compare
  let equal = ( = )
  let counter = ref 0

  let fresh () =
    incr counter;
    "ext" ^ string_of_int !counter

  let reset () = counter := 0
  let pp fmt i = Format.fprintf fmt "%s" i
  let toString s = s
  let show = toString
end

module ExtSyn (Global : Global.GLOBAL.GLOBAL) = Make_Syntax (struct
  module Cid = ExtIdx ()
  module Mid = ExtIdx ()

  module Tag = struct
    type t = Tag
  end

  module Global = Global
end)

module type EXTSYN = sig
  module Global : Global.GLOBAL.GLOBAL
  include module type of ExtSyn (Global)
end

include Sgn
include SGN
