(* # 1 "src/lambda/Fgnopntable.sig.ml" *)

(* # 1 "src/lambda/Fgnopntable.fun.ml" *)
open! Basis
open Fgnopn

module FgnOpnTable (FgnOpnTable__0 : sig
  (* Extensible operation on foreign matter *)
  (* Author: Aleksey Kliger *)
  type arg
  type result
end) :
  FGN_OPN
    with type arg = FgnOpnTable__0.arg
     and type result = FgnOpnTable__0.result
