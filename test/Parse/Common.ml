type form = Term | Cmd1 | Cmd | Decl | Term1

type case = {
  name : string;
  form : form;
  input : string;
  skip : bool;
  failure : bool;
}
(** A test case is a plain description, so that the same corpus can drive both
    the behaviour assertions ({!behaviour_case}) and the source-position
    assertions ({!position_case}) without duplicating any input. *)

let test ?(skip = false) ?(failure = false) (name : string) (form : form)
    (input : string) : case =
  { name; form; input; skip; failure }

(* One-time, idempotent harness setup. This used to run once per [test] call,
   which registered a duplicate stderr sink for every case in the corpus. *)
let () =
  Printexc.record_backtrace true;
  Fmt_tty.setup_std_outputs ();
  Display.register (fun m ->
      let _ = Display.fmt Fmt.stderr (Display.Info.body_to_form m.msg) in
      Lwt.return ())

let show_input (input : string) : unit =
  Display.warning
    Display.Form.(
      concat
        [
          style Style.bold @@ style Style.Fore.red @@ string "Test input>>";
          nl ();
          string input;
          nl ();
          style Style.bold @@ style Style.Fore.red @@ string "<<Test input";
          nl ();
        ])

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

(** Does the input parse (or fail to parse) as expected? *)
let behaviour_case (c : case) : unit Alcotest.test_case =
  Alcotest.test_case c.name `Slow (fun () ->
      if c.skip then Alcotest.skip ()
      else
        match test_value c.form c.input with
        | None when c.failure ->
            show_input c.input;
            Alcotest.fail "Expected failure, but test passed"
        | Some e when not c.failure ->
            show_input c.input;
            Alcotest.failf
              "Expected success, but test failed with exception: %s"
              (Printexc.to_string e)
        | None | Some _ -> ())

(* Parse [input] keeping the result, and walk it for ghost positions.
   [debug_parser] is polymorphic ('a t -> string -> 'a), so the tree comes back
   directly. *)
let ghosts (f : form) (input : string) : string list =
  let open Modern.Modern in
  match f with
  | Term -> Positions.walk_term [] (debug_parser (parse_expr ()) input)
  | Term1 -> Positions.walk_term [] (debug_parser (parse_expr1 ()) input)
  | Decl -> Positions.walk_decl [] (debug_parser (parse_decl ()) input)
  | Cmd1 ->
      Positions.walk_cmd [] (debug_parser (Modern.Debug_Cmd.parse1 ()) input)
  | Cmd ->
      debug_parser (Modern.Debug_Cmd.parse ()) input
      |> List.mapi (fun i c -> Positions.walk_cmd [ Printf.sprintf "[%d]" i ] c)
      |> List.concat

(** Does every node of the parse tree carry a non-ghost source position?

    This asserts only that positions are {e present}, never that they are
    correct: a location of [(1000, 1)] on a four-line input passes. Most of
    these are expected to fail today -- see {!Positions} for why, and note in
    particular that command-level findings are structural (the concrete CST has
    no location field for them) rather than parser bugs. *)
let position_case (c : case) : unit Alcotest.test_case =
  Alcotest.test_case c.name `Slow (fun () ->
      (* A case that is expected not to parse has no tree to inspect. *)
      if c.skip || c.failure then Alcotest.skip ()
      else
        match ghosts c.form c.input with
        | [] -> ()
        | found ->
            show_input c.input;
            Alcotest.failf "ghost position(s) at:@\n  %s"
              (String.concat "\n  " found)
        | exception exn ->
            (* Distinguished from a ghost finding on purpose: [Term.view] has no
               [MacroParam_] branch and [Cmd.view] raises on [Seq_], so a view
               gap must not be reported as a missing position. *)
            show_input c.input;
            Alcotest.failf "position walk raised: %s" (Printexc.to_string exn))
