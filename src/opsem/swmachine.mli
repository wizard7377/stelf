(* # 1 "src/opsem/swmachine.sig.ml" *)

(* # 1 "src/opsem/swmachine.fun.ml" *)
open! Trace
open! Absmachine
open! Basis

module SwMachine (SwMachine__0 : sig
  module Trace : TRACE
  module AbsMachine : ABSMACHINE
  module TMachine : ABSMACHINE
end) : ABSMACHINE
