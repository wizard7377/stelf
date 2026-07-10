type form = Term | Cmd1 | Cmd | Decl | Term1

let test_value (f : form) (input : string) : exn option =
  let p : unit Modern.Modern.Parser.t =
    match f with
    | Term -> Modern.Modern.Parser.(Modern.Modern.parse_expr () *> return ())
    | Cmd1 -> Modern.Modern.Parser.(Modern.Debug_Cmd.parse1 () *> return ())
    | Cmd -> Modern.Modern.Parser.(Modern.Debug_Cmd.parse () *> return ())
    | Decl -> Modern.Modern.Parser.(Modern.Modern.parse_decl () *> return ())
    | Term1 -> Modern.Modern.Parser.(Modern.Modern.parse_expr1 () *> return ())
  in
  try
    Modern.Modern.debug_parser p input;
    None
  with exn -> Some exn

let test ?(skip = false) ?(failure = false) (name : string) (f : form)
    (input : string) : unit Alcotest.test_case =
  let () = Printexc.record_backtrace true in
  let () = Fmt_tty.setup_std_outputs () in
  let () =
    Display.register (fun m ->
        let _ = Display.fmt Fmt.stderr (Display.Info.body_to_form m.msg) in
        Lwt.return ())
  in
  Alcotest.test_case name `Slow (fun () ->
      let bad () =
        Display.warning
          Display.Form.(
            concat
              [
                style Style.bold @@ style Style.Fore.red
                @@ string "Test input>>";
                nl ();
                string input;
                nl ();
                style Style.bold @@ style Style.Fore.red
                @@ string "<<Test input";
                nl ();
              ])
      in
      if skip then Alcotest.skip ()
      else
        match test_value f input with
        | None when failure ->
            bad ();
            Alcotest.fail "Expected failure, but test passed"
        | Some e when not failure ->
            bad ();
            Alcotest.failf
              "Expected success, but test failed with exception: %s"
              (Printexc.to_string e)
        | None | Some _ -> ())
