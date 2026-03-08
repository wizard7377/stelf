open! Basis

module type SIGINT = sig
  val interruptLoop : (unit -> unit) -> unit
end
(* signature SIGINT *)
