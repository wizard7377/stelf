exception Interrupted

let () =
  Printexc.register_printer (function
    | Interrupted -> Some "Interrupted"
    | _ -> None)

module Repl (M : REPL.S) : REPL.REPL = struct
  let msgs : Display.Info.t list ref = ref []

  let add_msg (m : Display.Info.t) =
    if (not M.mute) && M.verbosity >= m.level then msgs := m :: !msgs

  let flush_msgs () : Display.Info.t array Lwt.t =
    Lwt_mutex.with_lock Display.lock (fun _ ->
        let pending = Array.of_list (List.rev !msgs) in
        msgs := [];
        Lwt.return pending)

  let () = Display.register (fun m -> Lwt.return @@ add_msg m)

  type response = Continue | Fail of string | Stop

  let term : LTerm.t ref Lwt.t = Lwt.map ref @@ Lazy.force LTerm.stdout
  let history : LTerm_history.t = LTerm_history.create []

  let ends_with_terminator s =
    let len = String.length s in
    let i = ref (len - 1) in
    while
      !i >= 0
      &&
      let c = s.[!i] in
      c = ' ' || c = '\t' || c = '\r'
    do
      decr i
    done;
    !i >= 1 && s.[!i] = '.' && s.[!i - 1] = '%'

  let make_prompt str =
    React.S.const
      (LTerm_text.eval
         [
           LTerm_text.B_bold true;
           LTerm_text.B_fg LTerm_style.lgreen;
           LTerm_text.S str;
           LTerm_text.E_fg;
           LTerm_text.E_bold;
         ])

  let read_line t prompt_str : string Lwt.t =
    let open Lwt.Syntax in
    let rl =
      object (self)
        inherit
          LTerm_read_line.read_line ~history:(LTerm_history.contents history) ()

        inherit [Zed_string.t] LTerm_read_line.term t
        initializer self#set_prompt (make_prompt prompt_str)
      end
    in
    let* s = rl#run in
    Lwt.return (Zed_string.to_utf8 s)

  exception Interrupted = Interrupted
  let stop code = exit code

  let display_color_style (color : Display.color) : LTerm_style.color = match color with
    | Display.Info.Black -> LTerm_style.black
    | Display.Info.Red -> LTerm_style.red
    | Display.Info.Green -> LTerm_style.green
    | Display.Info.Yellow -> LTerm_style.yellow
    | Display.Info.Blue -> LTerm_style.blue
    | Display.Info.Magenta -> LTerm_style.magenta
    | Display.Info.Cyan -> LTerm_style.cyan
    | Display.Info.White -> LTerm_style.white
    | Display.Info.Bright_black -> LTerm_style.black
    | Display.Info.Bright_red -> LTerm_style.red
    | Display.Info.Bright_green -> LTerm_style.green
    | Display.Info.Bright_yellow -> LTerm_style.yellow
    | Display.Info.Bright_blue -> LTerm_style.blue
    | Display.Info.Bright_magenta -> LTerm_style.magenta
    | Display.Info.Bright_cyan -> LTerm_style.cyan
    | Display.Info.Bright_white -> LTerm_style.white
    | Display.Info.Rgb (r, g, b) -> LTerm_style.rgb r g b
  let stylize' (span : Display.span) : LTerm_style.t = 
    { LTerm_style.none with bold = Some span.style.bold; underline = Some span.style.underline; foreground = Option.map display_color_style span.style.foreground ; background = Option.map display_color_style span.style.background   }
  let span_to_ltext (span : Display.span) : LTerm_text.t =
      LTerm_text.stylise  span.text (stylize' span)
  let render_msg (m : Display.t) : unit Lwt.t = match m.msg with 
  | Fmt fmt -> let flush, put = LTerm_text.make_formatter () in
              fmt put;
              let text = flush () in 
              Lwt.bind term (fun term' -> LTerm.fprintls !term' text)
  | Rich rich -> let text = (List.map span_to_ltext rich) in
                 Lwt.bind term (fun term' -> Lwt_list.iter_s (LTerm.fprints !term') text)
  let flush () : unit Lwt.t =
    let open Lwt.Syntax in
    let* pending = flush_msgs () in
    let* () = Lwt_list.iter_s render_msg (Array.to_list pending) in
    let* term' = term in
    let* () = LTerm.flush !term' in
    Lwt.return ()

  let report_error_exn (exn : exn) : unit Lwt.t =
    render_msg
      (Display.Info.msg ~kind:Display.Info.Error (fun ppf ->
           Format.pp_print_string ppf (Printexc.to_string exn)))

  let rec read : (string -> response Lwt.t) -> int Lwt.t =
   fun f ->
    let open Lwt.Syntax in
    let* term' = term in
    let rec read_multiline (acc : string) : string Lwt.t =
      let prompt = if String.equal acc "" then "λΠ> " else "  > " in
      let* line = read_line !term' prompt in
      let full = if String.equal acc "" then line else acc ^ "\n" ^ line in
      if ends_with_terminator full || String.equal (String.trim full) "" then
        Lwt.return full
      else read_multiline full
    in
    Lwt.catch
      (fun () ->
        let* () = flush () in
        let* r0 = read_multiline "" in
        let* continue =
          try f r0 with
          | Sys.Break -> Lwt.return Stop
          | exn ->
              let* () = report_error_exn exn in
              Lwt.return Continue
        in
        match continue with
        | Continue -> read f
        | Fail msg ->
            Printf.eprintf "Error: %s\n%!" msg;
            let* () = flush () in
            Lwt.return 1
        | Stop ->
            let* () = flush () in
            Lwt.return 0)
      (fun exn ->
        match exn with
        (* Ctrl-C ([Interrupt]) and EOF/Ctrl-D ([End_of_file], also raised when
           stdin is a closed pipe or redirected file) both mean "the reader is
           done": exit cleanly rather than reporting and retrying — the latter
           would spin forever, since stdin stays at EOF on every re-read. *)
        | LTerm_read_line.Interrupt | End_of_file ->
            let* () = flush () in
            Lwt.return 0
        | exn ->
            let* () = report_error_exn exn in
            let* () = flush () in
            read f)

  let show _fmt = () (* Format.pp_print_string fmt "λΠ> " *)
end
