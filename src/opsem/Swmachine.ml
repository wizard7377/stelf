(* # 1 "src/opsem/Swmachine.sig.ml" *)

(* # 1 "src/opsem/Swmachine.fun.ml" *)
open! Trace
open! Absmachine
open! Basis

module SwMachine (SwMachine__0 : sig
  module Trace : TRACE
  module AbsMachine : ABSMACHINE
  module TMachine : ABSMACHINE
end) : ABSMACHINE = struct
  open SwMachine__0

  (*! structure IntSyn = AbsMachine.IntSyn !*)
  (*! structure CompSyn = AbsMachine.CompSyn !*)
  let rec solve args =
    begin if Trace.tracing () then TMachine.solve args
    else AbsMachine.solve args
    end
end
(*! sharing TMachine.IntSyn = AbsMachine.IntSyn !*)
(*! sharing TMachine.CompSyn = AbsMachine.CompSyn !*)
(* functor SwMachine *)

(* # 1 "src/opsem/Swmachine.sml.ml" *)
