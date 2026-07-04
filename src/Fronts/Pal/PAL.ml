module type PAL' = sig
  module M : IMPL.IMPL

  val install : M.Cst.cmd -> unit
  val parse : string -> M.Cst.cmd list
  val exec : string -> unit
end

module type PAL = sig
  module M : IMPL.IMPL

  exception Error of exn

  module Start () : PAL' with module M = M

  val status_to_exit : M.status -> int
  val make : M.source -> M.status
  val top : ?config:Fpath.t -> (module Tui.REPL.S) -> int Lwt.t
  val run : unit -> unit
end
