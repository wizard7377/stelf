module type PAL' = sig
  module M : IMPL.IMPL

  val install : M.Cst.cmd -> Reply.t list
  val parse : string -> M.Cst.cmd list
  val exec : string -> Reply.t list
end

module type PAL = sig
  module M : IMPL.IMPL

  exception Error of exn

  module Start () : PAL' with module M = M

  val status_to_exit : M.status -> int
  val make : M.source -> Reply.outcome
  val top : ?config:Fpath.t -> (module Tui.REPL.S) -> int Lwt.t
  val run : unit -> unit
  val simulate : string -> bool Lwt.t
  val render : ?config:Fpath.t -> (module Tui.REPL.S) -> string -> unit
end
