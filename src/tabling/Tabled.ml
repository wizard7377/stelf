(* # 1 "src/tabling/Tabled.sig.ml" *)

(* # 1 "src/tabling/Tabled.fun.ml" *)

(* # 1 "src/tabling/Tabled.sml.ml" *)
open! Basis

module TabledSyn =
  Tabledsyn.MakeTabledSyn
    (Names)
    (TableInstances.IntRedBlackTree)
    (Index)
