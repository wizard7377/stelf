(* # 1 "src/frontend/Unknownexn.sig.ml" *)
open! Basis

module type UNKNOWN_EXN = sig
  val unknownExn : exn -> string
end
