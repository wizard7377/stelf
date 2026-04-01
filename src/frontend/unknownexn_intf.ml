(* # 1 "src/frontend/unknownexn.sig.ml" *)
open! Basis

module type UNKNOWN_EXN = sig
  val unknownExn : exn -> string
end
