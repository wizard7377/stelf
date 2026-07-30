(* No [version] here on purpose: it would be a second, hardcoded source of truth.
   The version lives in [Pal.M.version], which the executable sets from
   dune-build-info. *)

let logo = Logo.logo

module type PAL = PAL.PAL
module type PAL' = PAL.PAL'

module Opts = Opts
module Reply = Reply
module Render = Render
module Help = Help

exception Error of exn

let () =
  Printexc.register_printer (function
    | Error exn -> Some (Printexc.to_string exn)
    | _ -> None)

module Pal : PAL.PAL = struct
  module M = Impl.Impl ()

  module type S = module type of M

  let status_to_exit : M.status -> int = function M.Ok -> 0 | M.Abort -> 1
  let make = M.make

  exception Error = Error

  module Start () = struct
    module M = struct
      include M

      let () = Install.reset ()
    end

    let ns = ref (M.Names.newNamespace ())
    let loc = ref M.Cst.View.ghost
    let install (cmd : M.Cst.cmd) : Reply.t list = M.Install.install1 !ns cmd

    let parse (s : string) : M.Cst.cmd list =
      M.Cmd.Modern.run (M.Cmd.parse ()) ns !loc s

    let exec (s : string) : Reply.t list = M.Install.install !ns (parse s)
  end

  let top ?config (module N : Tui.REPL.S) =
    let module Pal = Start () in
    let module R = Tui.Repl.Repl (N) in
    M.mode := `Repl;
    M.chatter := Display.Info.to_chatter N.verbosity;
    (match config with
    | Some f -> ignore (Render.report (M.make (M.File f)))
    | None -> ());
    R.read (fun l ->
        let replies = Pal.exec l in
        Render.replies replies;
        if Reply.quit_requested replies then Lwt.return R.Stop
        else Lwt.return R.Continue)

  let simulate (s : string) : bool Lwt.t =
    let module Pal = Start () in
    let replies = Pal.exec s in
    Lwt.return @@ not @@ Reply.quit_requested replies

  let render ?config (module N : Tui.REPL.S) (s : string) : unit =
    assert false (* TODO *)

  let run () = ()
end
