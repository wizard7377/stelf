open! Table
open! Names.Names_
open! Index.Index_

(* # 1 "src/tabling/Tabled.sig.ml" *)

(* # 1 "src/tabling/Tabled.fun.ml" *)

(* # 1 "src/tabling/Tabled.sml.ml" *)

module TabledSyn =
  Tabledsyn.MakeTabledSyn (Names) (TableInstances.IntRedBlackTree) (Index)
