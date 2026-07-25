(* # 1 "src/opsem/Swmachine.sig.ml" *)

(* # 1 "src/opsem/Swmachine.fun.ml" *)
open! Trace
open! Absmachine
open! Basis

module SwMachine (SwMachine__0 : sig
  module Trace : TRACE
  module AbsMachine : ABSMACHINE
  module TMachine : ABSMACHINE
end) : ABSMACHINE
