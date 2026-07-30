(* The stelf command line.

   The [pal] library is wrapped and its interface module is Pal.ml, so the proof
   assistant itself is the inner [Pal.Pal]. [P] names the library, [Assistant]
   the assistant. Note that [Pal.logo] also happens to resolve after an
   [open P.Pal] — the name [Pal] still finds the outer library module — but that
   is an accident that breaks the moment anyone writes [open Pal], so everything
   here goes through [P] and [Assistant] and the distinction stays visible. *)

module P = Pal
module Assistant = P.Pal
open Cmdliner
open Cmdliner.Term.Syntax

(* The version comes from dune-build-info, and that is why [bin/] is the only
   part of the tree depending on it: the real value is written into *this
   executable* by dune's artifact substitution, which rewrites a placeholder at
   install or promote time. A library compiled once and linked into several
   frontends has nothing to substitute, so no library can source this.

   [Build_info.V1.version ()] is documented to be [None] during development --
   substitution has not run -- so a plain `dune build` reports "dev" rather than
   a misleading number. `dune install` / `dune build --promote-install-files`
   report the package version. *)
let version =
  match Build_info.V1.version () with
  | Some v -> Build_info.V1.Version.to_string v
  | None -> "dev"

(* Impl reads this for [%version]; assigning it once here, at module
   initialisation, covers every subcommand -- including REPL sessions, since
   [Install.reset ()] deliberately does not clear it. *)
let () = Assistant.M.version := version

(* ------------------------------------------------------------------------- *)
(* Terminal setup                                                            *)
(* ------------------------------------------------------------------------- *)

(* Fmt_tty.setup_std_outputs resolves TERM and isatty for us and records the
   verdict on Fmt.stdout; reading it back is how bin/ decides about colour with
   no unix dependency of its own and no duplicated policy. Fmt.stdout is a
   DIFFERENT formatter from Format.std_formatter even though both wrap the stdout
   channel — it is only ever queried here, never printed to, so the two buffers
   cannot interleave.

   Only the paths that print the banner through a plain Format formatter call
   this. The REPL must not: its output goes through LTerm_text.make_formatter,
   where a raw escape is just text, and colour there is already handled by
   Tui.REPL.S.use_color. Nor must [check]: its output is asserted byte for byte
   by the cram tests in test/STELF. *)
let setup_tty () =
  Fmt_tty.setup_std_outputs ();
  Display.set_color (Fmt.style_renderer Fmt.stdout = `Ansi_tty)

(* Display.fmt only queues. Format flushes std_formatter from an at_exit, which
   is late enough that the last logo row can be emitted after the shell has
   drawn its prompt; and the art carries no trailing break of its own, so the
   prompt would land on the last row. Break and flush here. *)
let print_logo () =
  Display.fmt Format.std_formatter P.logo;
  Format.fprintf Format.std_formatter "@\n%!"

(* ------------------------------------------------------------------------- *)
(* Documentation vocabulary shared by every command                          *)
(* ------------------------------------------------------------------------- *)

let sdocs = Manpage.s_common_options

(* Section titles used as [~docs] values, to split the COMMANDS listing in two.
   The group fixes their order by naming them in its own [~man]. *)
let s_project = "PROJECT COMMANDS"
let s_info = "INFORMATION COMMANDS"

(* Cmd.Exit.defaults documents 0, 123, 124 and 125. Every command here returns
   [status_to_exit], which is 0 or 1, so 1 needs describing too. *)
let exits =
  Cmd.Exit.info 1
    ~doc:
      "on a STELF error: a file failed to check, or a project could not be \
       created."
  :: Cmd.Exit.defaults

let common_man =
  [
    `S Manpage.s_common_options;
    `P "These options are understood by every $(mname) command.";
    `S "MORE HELP";
    `P
      "Use $(mname) $(i,COMMAND) $(b,--help) for help on a single command, or \
       equivalently $(mname) $(b,help) $(i,COMMAND).";
    `Noblank;
    `P
      "Inside the REPL, $(b,%help %.) lists every $(b,%)-command with a \
       one-line summary.";
    `Noblank;
    `P "The full reference is at https://standardocaml.github.io/";
    `S Manpage.s_bugs;
    `P "Report issues at https://github.com/standardocaml/stelf/issues.";
  ]

(* ------------------------------------------------------------------------- *)
(* Diagnostics                                                               *)
(* ------------------------------------------------------------------------- *)

(* Diagnostic sink for the non-interactive paths: Display messages become Grace
   diagnostics on stdout.

   Deliberately NOT shared with src/Fronts/Tui/Repl.ml. That renderer targets
   LTerm styled text, and the only thing the two have in common is the
   three-line kind-to-severity mapping; sharing it would mean a new module in
   [pal] or [tui] that both depend on — cross-library surgery for no reduction
   in real logic.

   The [\n] in the Response case is a literal newline, not [@\n]: the cram tests
   in test/STELF assert this output byte for byte, and pp_force_newline can shift
   downstream box indentation. *)
let register_cli_diagnostics ~(verbosity : Display.Info.level) ~(mute : bool) ()
    =
  Display.register (fun (m : Display.Info.t) ->
      if (not mute) && m.level <= verbosity then begin
        let open Grace.Diagnostic.Severity in
        let pp_diag fmt d = Grace_ansi_renderer.pp_diagnostic fmt d in
        let body = Display.Info.body_to_form m.msg in
        let display_diag sev =
          let diag =
            Grace.Diagnostic.create sev (fun ppf -> Display.fmt ppf body)
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

      Lwt.return ())

(* ------------------------------------------------------------------------- *)
(* stelf repl                                                                *)
(* ------------------------------------------------------------------------- *)

let repl_cmd : int Cmd.t =
  let config_file =
    Arg.(
      value
      & pos 0 (some file) None
      & info [] ~docv:"CONFIG"
          ~doc:
            "Optional $(b,stelf.toml) project file to load before entering the \
             REPL.")
  in
  let doc = "Start the interactive REPL" in
  let man =
    [
      `S Manpage.s_description;
      `P
        "Reads $(b,%)-commands from the terminal and evaluates them against a \
         live signature.";
      `P
        "A command is submitted only when it ends with the separator $(b,%.), \
         so input may span as many lines as you like; the continuation prompt \
         is $(b,>). Type $(b,%help %.) for the list of commands, and \
         $(b,%quit %.) or Ctrl-D to leave.";
      `P
        "If $(i,CONFIG) is given it is loaded first, exactly as $(mname) \
         $(b,check) would load it.";
      `S Manpage.s_examples;
      `Pre "  \\$ $(mname) repl";
      `Noblank;
      `Pre "  \\$ $(mname) repl stelf.toml";
      `Noblank;
      `Pre "  \\$ $(mname) repl --debug";
      `S Manpage.s_see_also;
      `P "$(mname) $(b,check)";
      `Blocks common_man;
    ]
  in
  Cmd.v
    (Cmd.info "repl" ~doc ~docs:s_project ~sdocs ~exits ~man)
    (let+ verbosity = Arg.value P.Opts.Opts.verbosity
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
     Lwt_main.run
       (Assistant.top ?config:(Option.map Fpath.v config) (module N)))

(* ------------------------------------------------------------------------- *)
(* stelf check                                                               *)
(* ------------------------------------------------------------------------- *)

let check_cmd : int Cmd.t =
  let file =
    Arg.(
      required
      & pos 0 (some file) None
      & info [] ~docv:"FILE"
          ~doc:
            "The file to check: a $(b,stelf.toml) project file, a legacy \
             $(b,.cfg), or a single $(b,.lf) source file.")
  in
  let doc = "Type check a STELF file or project" in
  let man =
    [
      `S Manpage.s_description;
      `P
        "Loads $(i,FILE) and runs it through the whole pipeline — parsing, \
         reconstruction, type checking, and whatever mode, world, coverage and \
         totality checks it declares — then exits. Diagnostics are reported \
         with source spans.";
      `P
        "Give a $(b,stelf.toml) to check a project including its dependencies; \
         give an $(b,.lf) file to check just that file.";
      `S Manpage.s_examples;
      `Pre "  \\$ $(mname) check stelf.toml";
      `Noblank;
      `Pre "  \\$ $(mname) check src/main.lf";
      `Noblank;
      `Pre "  \\$ $(mname) check -v stelf.toml";
      `S Manpage.s_see_also;
      `P "$(mname) $(b,repl)";
      `Blocks common_man;
    ]
  in
  Cmd.v
    (Cmd.info "check" ~doc ~docs:s_project ~sdocs ~exits ~man)
    (let+ verbosity = Arg.value P.Opts.Opts.verbosity
     and+ mute = Arg.value P.Opts.Opts.mute
     and+ f = file in
     (* Grace's ANSI renderer needs this; the Display colour flag deliberately
        stays off here, so this output remains byte-identical for the cram
        tests. *)
     Fmt_tty.setup_std_outputs ();
     Assistant.M.chatter := Display.Info.to_chatter verbosity;
     register_cli_diagnostics ~verbosity ~mute ();
     Assistant.status_to_exit @@ P.Render.report
     @@ Assistant.M.make (Assistant.M.File (Fpath.v f)))

(* ------------------------------------------------------------------------- *)
(* stelf setup                                                               *)
(* ------------------------------------------------------------------------- *)

let setup_cmd : int Cmd.t =
  let name =
    Arg.(
      required
      & pos 0 (some string) None
      & info [] ~docv:"NAME"
          ~doc:
            "Name of the new project. A directory of this name is created, and \
             it is substituted for $(b,{{name}}) throughout the template.")
  in
  let path =
    Arg.(
      value
      & pos 1 (some dir) None
      & info [] ~docv:"PATH"
          ~doc:
            "Existing directory to create the project $(i,in); the project \
             itself is $(i,PATH)/$(i,NAME). Defaults to the current directory.")
  in
  let doc = "Create a new STELF project" in
  let man =
    [
      `S Manpage.s_description;
      `P
        "Writes a project skeleton — $(b,stelf.toml), a $(b,README.md), and a \
         $(b,src/main.lf) — into a new $(i,NAME) directory. The command fails \
         rather than overwrite anything if $(i,NAME) already exists.";
      `P
        "The result is ready for $(mname) $(b,check) and $(mname) $(b,repl); \
         both accept the generated $(b,stelf.toml) directly.";
      `S Manpage.s_examples;
      `Pre "  \\$ $(mname) setup hello";
      `Noblank;
      `Pre "  \\$ $(mname) setup hello ~/projects";
      `S Manpage.s_see_also;
      `P "$(mname) $(b,check)";
      `Blocks common_man;
    ]
  in
  Cmd.v
    (Cmd.info "setup" ~doc ~docs:s_project ~sdocs ~exits ~man)
    (let+ name = name
     and+ path = path in
     match Setup.setup ?dir:(Option.map Fpath.v path) name with
     | Ok () -> 0
     | Error (`Msg m) ->
         Format.eprintf "stelf setup: %s@." m;
         1)

(* ------------------------------------------------------------------------- *)
(* stelf version                                                             *)
(* ------------------------------------------------------------------------- *)

let version_cmd : int Cmd.t =
  let doc = "Print the version and the STELF banner" in
  let man =
    [
      `S Manpage.s_description;
      `P
        "Prints $(mname)'s version followed by the STELF banner. The banner is \
         coloured when standard output is a terminal and plain otherwise, so it \
         is safe in a pipe.";
      `P "$(mname) $(b,--version) prints the bare version string, with no banner.";
      `S Manpage.s_examples;
      `Pre "  \\$ $(mname) version";
      `Blocks common_man;
    ]
  in
  Cmd.v
    (Cmd.info "version" ~doc ~docs:s_info ~sdocs ~exits ~man)
    (let+ () = Term.const () in
     setup_tty ();
     (* One formatter throughout, so the banner cannot be reordered ahead of the
        version line. *)
     Format.printf "STELF version %s@." version;
     print_logo ();
     0)

(* ------------------------------------------------------------------------- *)
(* stelf help                                                                *)
(* ------------------------------------------------------------------------- *)

(* Term.ret is the only way to reach cmdliner's own man-page printer from user
   code: the term evaluates to [`Help (format, topic)] and cmdliner — which owns
   the pages — does the rendering. The interface calls this API discouraged but
   offers no replacement, and it is the shape cmdliner's own documentation uses
   for exactly this command. *)
let help_cmd : int Cmd.t =
  let topic =
    Arg.(
      value
      & pos 0 (some string) None
      & info [] ~docv:"COMMAND"
          ~doc:
            "The $(mname) command whose manual page to show. Omit it for the \
             manual page of $(mname) itself.")
  in
  let help_fn (fmt : Manpage.format) (cmds : string list)
      (topic : string option) : int Term.ret =
    match topic with
    | None -> `Help (fmt, None)
    | Some t when List.mem t cmds -> `Help (fmt, Some t)
    | Some t ->
        (* Deliberately not [`Error]: Cmd.eval''s [?term_err] governs the exit
           code for BOTH [`Help] and [`Error] returned from a Term.ret, so
           setting it to keep help at 0 would also make an unknown command exit
           0. Reporting the error here and returning [`Ok 1] keeps the two
           independent. *)
        Format.eprintf "stelf help: unknown command %S: expected one of %s@." t
          (String.concat ", " (List.sort String.compare cmds));
        `Ok 1
  in
  let doc = "Show the manual page for a command" in
  let man =
    [
      `S Manpage.s_description;
      `P
        "$(iname) prints the manual page of $(i,COMMAND) — the same page as \
         $(mname) $(i,COMMAND) $(b,--help). With no argument it prints the \
         manual page of $(mname) itself.";
      `P
        "This is help for the command line. For the REPL's $(b,%)-commands, \
         start $(mname) $(b,repl) and type $(b,%help %.).";
      `S Manpage.s_examples;
      `Pre "  \\$ $(mname) help";
      `Noblank;
      `Pre "  \\$ $(mname) help check";
      `Noblank;
      `Pre "  \\$ $(mname) help --man-format=groff setup";
      `Blocks common_man;
    ]
  in
  Cmd.v
    (Cmd.info "help" ~doc ~docs:s_info ~sdocs ~exits ~man)
    Term.(ret (const help_fn $ Arg.man_format $ choice_names $ topic))

(* ------------------------------------------------------------------------- *)
(* stelf                                                                     *)
(* ------------------------------------------------------------------------- *)

(* Bare [stelf]: banner, then the main manual page, rather than cmdliner's
   "required COMMAND is missing" error. The banner is printed as a side effect
   before returning [`Help] because cmdliner writes the page to
   Format.std_formatter — the same formatter print_logo flushes, so the ordering
   is guaranteed.

   [`Plain] rather than [`Pager]: a pager is a subprocess with its own stdout, so
   the banner and the page would interleave and the banner would be pointless. *)
let default_cmd : int Term.t =
  Term.ret
    (let+ () = Term.const () in
     setup_tty ();
     print_logo ();
     (`Help (`Plain, None) : int Term.ret))

let main_cmd : int Cmd.t =
  let doc = "The STELF proof assistant" in
  let man =
    [
      `S Manpage.s_description;
      `P
        "$(mname) is a proof assistant for the Edinburgh Logical Framework: an \
         OCaml port of Twelf with a new surface syntax. It type checks LF \
         signatures, checks modes, worlds, coverage and totality, answers \
         logic-programming queries, and provides an interactive REPL.";
      `P "Run with no command to see this page.";
      `S s_project;
      `S s_info;
      `S Manpage.s_examples;
      `Pre "  \\$ $(mname) setup hello";
      `Noblank;
      `Pre "  \\$ $(mname) check hello/stelf.toml";
      `Noblank;
      `Pre "  \\$ $(mname) repl hello/stelf.toml";
      `Blocks common_man;
    ]
  in
  Cmd.group ~default:default_cmd
    (Cmd.info "stelf" ~version ~doc ~sdocs ~exits ~man)
    [ repl_cmd; check_cmd; version_cmd; help_cmd; setup_cmd ]

let () = Basis.OS.Process.exit (Cmd.eval' main_cmd)
