(* # 1 "src/server/sigint.sig.ml" *)
open! Basis

module type SIGINT = sig
  val interruptLoop : (unit -> unit) -> unit
end
