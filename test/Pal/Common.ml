let setup_display () =
  Printexc.record_backtrace true;
  Logs.set_reporter (Logs_fmt.reporter ());
  Logs.set_level ~all:false (Some Logs.Debug);
  Fmt_tty.setup_std_outputs ();
  Display.register (fun m ->
      if Display.Info.( >= ) Display.Info.Normal m.level then begin
        let severity =
          let open Grace.Diagnostic.Severity in
          match m.kind with
          | Some Display.Info.Error -> Error
          | Some Warning -> Warning
          | Some Info | Some Debug | Some Response | None -> Note
        in
        let diag =
          Grace.Diagnostic.create severity (fun ppf ->
              Display.fmt ppf m.msg)
        in
        Grace_ansi_renderer.pp_diagnostic Format.std_formatter diag
      end;
      Lwt.return ())

let test ?(skip = false) ?(failure = false) (name : string) (cmds : string list)
    : string * unit Alcotest.test_case list =
  let () = setup_display () in
  let exec =
    lazy
      (let module P = Pal.Pal.Start () in
       P.exec)
  in
  let run cmd =
    try
      Printexc.record_backtrace true;
      (Lazy.force exec) cmd;
      None
    with e -> Some e
  in
  let has_failed = ref false in
  ( name,
    List.mapi
      (fun i cmd ->
        Alcotest.test_case
          (name ^ " - " ^ string_of_int (i + 1))
          `Slow
          (fun () ->
            if skip || !has_failed then Alcotest.skip ()
            else
              match run cmd with
              | None when failure ->
                  Alcotest.fail "Expected failure, but test passed"
              | Some e when not failure ->
                  let bt = Printexc.get_backtrace () in
                  has_failed := true;
                  Printf.eprintf "Exception: %s\nBacktrace:\n%s\n%!"
                    (Printexc.to_string e) bt;
                  Alcotest.failf
                    "Expected success, but test failed with exception: %s\n\
                     Backtrace:\n\
                     %s"
                    (Printexc.to_string e) bt
              | None | Some _ -> ()))
      cmds )

let file_test ?(skip = false) ?(failure = false) (name : string) (paths : string list)
    : string * unit Alcotest.test_case list =
  let () = setup_display () in
  let make =
    lazy
      (let module P = Pal.Pal.Start () in
       fun path ->
         let fp = Fpath.v path in
         match P.M.make (P.M.File fp) with
         | P.M.Ok -> None
         | P.M.Abort -> Some (Failure ("Abort loading " ^ path)))
  in
  let run path =
    try
      Printexc.record_backtrace true;
      (Lazy.force make) path
    with e -> Some e
  in
  let has_failed = ref false in
  ( name,
    List.mapi
      (fun i path ->
        Alcotest.test_case
          (name ^ " - " ^ string_of_int (i + 1))
          `Slow
          (fun () ->
            if skip || !has_failed then Alcotest.skip ()
            else
              match run path with
              | None when failure ->
                  Alcotest.fail "Expected failure, but test passed"
              | Some e when not failure ->
                  let bt = Printexc.get_backtrace () in
                  has_failed := true;
                  Printf.eprintf "Exception: %s\nBacktrace:\n%s\n%!"
                    (Printexc.to_string e) bt;
                  Alcotest.failf
                    "Expected success, but test failed with exception: %s\n\
                     Backtrace:\n\
                     %s"
                    (Printexc.to_string e) bt
              | None | Some _ -> ()))
      paths )
