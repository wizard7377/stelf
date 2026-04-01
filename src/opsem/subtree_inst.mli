(* # 1 "src/opsem/subtree_inst.sig.ml" *)

(* # 1 "src/opsem/subtree_inst.fun.ml" *)
open! Basis
open Abstract_tabled
open Memo_table

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
  module AbstractTabled : Abstract_tabled.ABSTRACTTABLED

  (*! sharing AbstractTabled.IntSyn = IntSyn' !*)
  module Print : PRINT
end) : MEMOTABLE
