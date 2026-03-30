(** Entry point for the STELF server executable. *)

module Twelf_server = Server.Server_.Server

(** Run the server process and return its exit code. *)
let run_server () : int = Twelf_server.server ("stelf", [])

let () = if run_server () = 0 then exit 0 else exit 1
