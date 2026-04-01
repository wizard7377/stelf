(* # 1 "src/netserver/netserver_.sig.ml" *)

(* # 1 "src/netserver/netserver_.fun.ml" *)

(* # 1 "src/netserver/netserver_.sml.ml" *)
open! Basis

module type NETSERVER = sig
  (* int argument is which port number to run on *)
  val flashServer : int -> unit

  (* Macromedia Flash XMLSocket interface *)
  val humanServer : int -> unit

  (* Human-readable interface, suitable for telnet *)
  (* second argument is what directory server.html is kept in *)
  val httpServer : int -> string -> unit

  (* HTTP interface, suitable for javascript XMLHttpRequest *)
  val setExamplesDir : string -> unit
end
