(* # 1 "src/server/server_.sig.ml" *)

(* # 1 "src/server/server_.fun.ml" *)

(* # 1 "src/server/server_.sml.ml" *)
open! Basis

(** Interactive command server for Stelf/STELF. *)

module type SERVER = sig
  val server : string * string list -> OS.Process.status
end
