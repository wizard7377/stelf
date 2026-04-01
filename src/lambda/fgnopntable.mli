(* # 1 "src/lambda/fgnopntable.sig.ml" *)

(* # 1 "src/lambda/fgnopntable.fun.ml" *)
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
