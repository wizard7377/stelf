(* # 1 "src/netserver/Netserver_.sig.ml" *)

(* # 1 "src/netserver/Netserver_.fun.ml" *)

(* # 1 "src/netserver/Netserver_.sml.ml" *)
open! Basis

module type NETSERVER = sig
  (* int argument is which port number to run on *)
  val flashServer : int -> unit

  (* Macromedia Flash XMLSocket interface *)
  val humanServer : int -> unit

  (* Human-readable interface, suitable for telnet *)
  (* second argument is what directory Server.html is kept in *)
  val httpServer : int -> string -> unit

  (* HTTP interface, suitable for javascript XMLHttpRequest *)
  val setExamplesDir : string -> unit
end
