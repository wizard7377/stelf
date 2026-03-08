open! Basis

(* Meta Global parameters *)
(* Author: Carsten Schuermann *)
module MTPData (MTPData__0 : sig
  module MTPGlobal : MTPGLOBAL
end) : MTPDATA = struct
  let maxFill = ref 0
end
(* structure MTPData*)
