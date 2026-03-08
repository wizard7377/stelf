open! Trace
open! Basis

module SwMachine (SwMachine__0 : sig
  module Trace : TRACE
  module AbsMachine : ABSMACHINE
  module TMachine : ABSMACHINE
end) : ABSMACHINE = struct
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
