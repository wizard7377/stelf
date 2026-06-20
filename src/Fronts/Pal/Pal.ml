let version = "0.1.0"

module type PAL = PAL.PAL
module type PAL' = PAL.PAL'

module Pal : PAL.PAL = struct
  module M = Impl.Impl ()

  module type S = module type of M

  let status_to_exit : M.status -> int = function M.Ok -> 0 | M.Abort -> 1

  exception Error of exn

  module Start () = struct
    module M = struct 
      include M
      let () = Install.reset ()
    end

    let ns = ref (M.Names.newNamespace ())
    let loc = ref M.Cst.View.ghost
    let install (cmd : M.Cst.cmd) : unit = M.Install.install1 !ns cmd

    let parse (s : string) : M.Cst.cmd list =
      M.Cmd.Modern.run (M.Cmd.parse ()) ns !loc s

    let exec (s : string) : unit = List.iter install (parse s)
  end

  let top (module N : Tui.REPL.S) =
    let module Pal = Start () in
    let module R = Tui.Repl.Repl (N) in
    M.mode := `Repl;
    R.read (fun l ->
        Pal.exec l;
        Lwt.return R.Continue)

  let run () : unit =
    begin
      let module TempM = struct
        let use_color = true
        let use_unicode = true
      end in
      let open Cmdliner in
      let open Cmdliner.Term.Syntax in
      (* Note: local 'Cmd' alias refers to Cmdliner.Cmd here *)
      let help_cmd : int Cmd.t =
        let help_info = Cmd.info "help" ~doc:"Display help information"
        and help_term : int Term.t =
          Term.(const 0)
          (* TODO *)
        in
        Cmd.v help_info help_term
      in
      let repl_cmd : int Cmd.t =
        let repl_fn : int Term.t =
          let+ verbosity = Arg.value Opts.Opts.verbosity
          and+ color = Arg.value Opts.Opts.color
          and+ unicode = Arg.value Opts.Opts.unicode in
          let module M = struct
            let use_color = color
            let use_unicode = unicode
            let verbosity = verbosity
          end in
          Lwt_main.run (top (module M))
        and repl_info : Cmd.info =
          Cmd.info "repl" ~doc:"Start the interactive REPL"
        in
        Cmd.v repl_info repl_fn
      in
      let load_cmd : int Cmd.t =
        begin
          let file =
            Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE")
          in
          Cmd.v
            (Cmd.info "check" ~doc:"Load a .cfg or source file")
            Term.(
              const (fun f ->
                  M.chatter := 1;
                  Display.register (fun m ->
                      let current = Display.Info.from_chatter !M.chatter in
                      if Display.Info.(m.level =< current) then
                        let _ = Display.fmt Fmt.stdout m.msg in
                        Lwt.return ()
                      else Lwt.return ());
                  status_to_exit @@ M.make (File (Fpath.v f)))
              $ file)
        end
      in
      let lsp_cmd : int Cmd.t =
        begin
          Cmd.v
            (Cmd.info "server" ~doc:"Start the LSP server (not yet implemented)")
            Term.(
              const (fun () ->
                  M.mode := `Lsp;
                  print_endline "LSP mode is not yet implemented.";
                  Basis.OS.Process.exit Basis.OS.Process.failure)
              $ const ())
        end
      in
      let legacy_cmd : int Cmd.t =
        Cmd.v (Cmd.info "legacy")
          Term.(
            const (fun () ->
                let module Twelf_server = Server.Server_.Server in
                Twelf_server.server ("stelf", []))
            $ const ())
      in
      let version_cmd : int Cmd.t =
        Cmd.v
          (Cmd.info "version" ~doc:"Display version information")
          Term.(
            const (fun () ->
                
                print_endline ("STELF version " ^ version);
                Fmt_tty.setup_std_outputs ();
                Display.fmt Format.std_formatter @@ Logo.logo; 
                0)
            $ const ())
      in
      let main_cmd =
        Cmd.group
          (Cmd.info "stelf" ~version ~doc:"The STELF proof assistant")
          [ repl_cmd; load_cmd; version_cmd; lsp_cmd; legacy_cmd ]
      in
      Basis.OS.Process.exit (Cmd.eval' main_cmd)
    end
end

(*let cmds = ModernImpl.run (Cmd.parse ()) ns loc line in
         List.app Install.install1 cmds; Lwt.return (Repl.Continue);*)
