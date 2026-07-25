(* # 1 "src/server/Sigint.sig.ml" *)
open! Basis

module type SIGINT = sig
  val interruptLoop : (unit -> unit) -> unit
end
