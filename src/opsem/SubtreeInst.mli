(* # 1 "src/opsem/SubtreeInst.sig.ml" *)

(* # 1 "src/opsem/SubtreeInst.fun.ml" *)
open! Basis
open AbstractTabled
open MemoTable

(* Linear Substitution Tree indexing *)
(* Linearity: Any variables occurring inside the substitution tree are linear *)
(* Any term we insert into the substitution tree is in normalform ! *)
(* Instance Checking *)
(* Author: Brigitte Pientka *)

module MemoTableInst (MemoTableInst__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn' !*)
  module Whnf : WHNF
  module Match : MATCH

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  (*! structure RBSet : RBSET !*)
  module Assign : ASSIGN

  (*! structure TableParam : TABLEPARAM !*)
  (*! sharing TableParam.IntSyn = IntSyn' !*)
  (*! sharing TableParam.CompSyn = CompSyn' !*)
  (*! sharing TableParam.RBSet = RBSet !*)
  module AbstractTabled : AbstractTabled_intf.ABSTRACTTABLED

  (*! sharing AbstractTabled.IntSyn = IntSyn' !*)
  module Print : PRINT
end) : MEMOTABLE
