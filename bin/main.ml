module P = Pal

let () =
  let open P.Pal in
  let open Cmdliner in
  let open Cmdliner.Term.Syntax in
  let version = P.version in
  let repl_cmd : int Cmd.t =
    let config_file =
      Arg.(
        value
        & pos 0 (some file) None
        & info [] ~docv:"CONFIG"
            ~doc:"Optional .toml project file to load before entering the REPL")
    in
    let repl_fn : int Term.t =
      let+ verbosity = Arg.value P.Opts.Opts.verbosity
      and+ mute = Arg.value P.Opts.Opts.mute
      and+ color = Arg.value P.Opts.Opts.color
      and+ unicode = Arg.value P.Opts.Opts.unicode
      and+ config = config_file in
      let module N = struct
        let use_color = color
        let use_unicode = unicode
        let verbosity = verbosity
        let mute = mute
      end in
      Lwt_main.run (top ?config:(Option.map Fpath.v config) (module N))
    and repl_info : Cmd.info =
      Cmd.info "repl"
        ~doc:"Start the interactive REPL, optionally loading a project config"
    in
    Cmd.v repl_info repl_fn
  in
  let check_cmd : int Cmd.t =
    let file = Arg.(required & pos 0 (some file) None & info [] ~docv:"FILE") in
    Cmd.v
      (Cmd.info "check" ~doc:"Load a .cfg or source file")
      Term.(
        const (fun verbosity mute f ->
            Fmt_tty.setup_std_outputs ();
            M.chatter := Display.Info.to_chatter verbosity;
            Display.register (fun m ->
                if (not mute) && m.level <= verbosity then begin
                  let open Grace.Diagnostic.Severity in
                  let pp_diag fmt d = Grace_ansi_renderer.pp_diagnostic fmt d in
                  let body = Display.Info.body_to_form m.msg in
                  let display_diag sev =
                    let diag =
                      Grace.Diagnostic.create sev (fun ppf ->
                          Display.fmt ppf body)
                    in
                    Format.printf "%a%!" pp_diag diag
                  in
                  match m.kind with
                  | Some Display.Error -> display_diag Error
                  | Some Display.Warning -> display_diag Warning
                  | Some Display.Response -> Format.printf "=> %t\n%!" body
                  | Some Display.Debug -> display_diag Note
                  | Some Display.Info -> display_diag Note
                  | _ -> display_diag Note
                end;

                Lwt.return ());
            status_to_exit @@ P.Render.report @@ M.make (File (Fpath.v f)))
        $ Arg.value P.Opts.Opts.verbosity
        $ Arg.value P.Opts.Opts.mute $ file)
  in
  let version_cmd : int Cmd.t =
    Cmd.v
      (Cmd.info "version" ~doc:"Display version information")
      Term.(
        const (fun () ->
            print_endline ("STELF version " ^ version);
            Fmt_tty.setup_std_outputs ();
            Display.fmt Format.std_formatter @@ Pal.logo;
            0)
        $ const ())
  in
  let help_cmd : int Cmd.t =
    Cmd.v
      (Cmd.info "help" ~doc:"Display help information")
      Term.(
        const (fun () ->
            print_endline ("STELF version " ^ version);
            Fmt_tty.setup_std_outputs ();
            Display.fmt Format.std_formatter @@ Pal.logo;
            0)
        $ const ())
    (* TODO Make this work *)
  in
  let setup_cmd : int Cmd.t =
    let name =
      Arg.(required & pos 0 (some string) None & info [] ~docv:"NAME")
    in
    Cmd.v
      (Cmd.info "setup" ~doc:"Create a new STELF project directory")
      Term.(
        const (fun name ->
            match Setup.setup name with
            | Ok () -> 0
            | Error (`Msg m) ->
                Format.eprintf "stelf setup: %s@." m;
                1)
        $ name)
  in
  let main_cmd =
    Cmd.group
      (Cmd.info "stelf" ~version ~doc:"The STELF proof assistant")
      [ repl_cmd; check_cmd; version_cmd; help_cmd; setup_cmd ]
  in
  Basis.OS.Process.exit (Cmd.eval' main_cmd)
