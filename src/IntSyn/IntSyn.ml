open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
module S = Syntax.IntSyn (Global_.Global)
include S.Ast
include S.Misc

let equal_cid (a : cid) (b : cid) = a = b
let compare_cid (a : cid) (b : cid) = compare a b
let pp_cid fmt c = Format.fprintf fmt "%d" c
let show_cid c = Int.toString c
let equal_mid (a : mid) (b : mid) = a = b
let compare_mid (a : mid) (b : mid) = compare a b
let pp_mid fmt m = Format.fprintf fmt "%d" m
let show_mid m = Int.toString m
let equal_csid (a : csid) (b : csid) = a = b
let compare_csid (a : csid) (b : csid) = compare a b
let pp_csid fmt c = Format.fprintf fmt "%d" c
let show_csid c = Int.toString c
let equal_head (a : head) (b : head) = a = b
let compare_head (a : head) (b : head) = compare a b
let pp_head fmt _ = Format.pp_print_string fmt "<head>"
let show_head _ = "<head>"
let equal_exp (a : exp) (b : exp) = a = b
let compare_exp (a : exp) (b : exp) = compare a b
let pp_exp fmt _ = Format.pp_print_string fmt "<exp>"
let show_exp _ = "<exp>"

module FgnExpStd = struct
  module ToInternal = Fgnopntable.FgnOpnTable (struct
    type nonrec arg = unit
    type nonrec result = exp
  end)

  module Map = Fgnopntable.FgnOpnTable (struct
    type nonrec arg = exp -> exp
    type nonrec result = exp
  end)

  module App = Fgnopntable.FgnOpnTable (struct
    type nonrec arg = exp -> unit
    type nonrec result = unit
  end)

  module EqualTo = Fgnopntable.FgnOpnTable (struct
    type nonrec arg = exp
    type nonrec result = bool
  end)

  module UnifyWith = Fgnopntable.FgnOpnTable (struct
    type nonrec arg = dec ctx * exp
    type nonrec result = fgnUnify
  end)

  let fold (csid : csid) (fe : fgnExp) (f : exp * 'a -> 'a) (b : 'a) : 'a =
    let r = ref b in
    let g u_ = r := f (u_, !r) in
    App.apply csid fe g;
    !r
end

module FgnCnstrStd = struct
  module ToInternal = Fgnopntable.FgnOpnTable (struct
    type nonrec arg = unit
    type nonrec result = (dec ctx * exp) list
  end)

  module Awake = Fgnopntable.FgnOpnTable (struct
    type nonrec arg = unit
    type nonrec result = bool
  end)

  module Simplify = Fgnopntable.FgnOpnTable (struct
    type nonrec arg = unit
    type nonrec result = bool
  end)
end

module Sgn = S.Sgn

let sgnReset = Sgn.reset
let sgnSize = Sgn.size
let sgnAdd = Sgn.add
let sgnLookup = Sgn.lookup
let sgnApp = Sgn.app
let sgnStructAdd = Sgn.structAdd
let sgnStructLookup = Sgn.structLookup
let constType = Sgn.constType
let constDef = Sgn.constDef
let constImp = Sgn.constImp
let constStatus = Sgn.constStatus
let constUni = Sgn.constUni
let constBlock = Sgn.constBlock
let ctxDec = S.Sgn.ctxDec
let blockDec = S.Sgn.blockDec
