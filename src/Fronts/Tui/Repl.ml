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

  (* Message rendering. Styling is expressed as [LTerm_style.t] values and
     handed to LTerm via [LTerm_text.make_formatter]: semantic tags
     ([@{<error>...@}], [@{<warning>...@}], etc.) inside a [Display.Info.t.msg]
     thunk, and the tag wrapping the [kind] prefix ("error: ", "=> ", ...), are
     resolved by [color_of_tag] into styles that LTerm encodes for the terminal.
     When [M.use_color] is false we pass no [read_color], so tags are ignored and
     the output is unstyled but textually correct. *)

  let color_of_tag : string -> LTerm_style.t =
    let open LTerm_style in
    function
    | "error" -> { none with bold = Some true; foreground = Some red }
    | "warning" -> { none with bold = Some true; foreground = Some yellow }
    | "response" ->
        { none with bold = Some true; foreground = Some (rgb 255 165 0) }
    (* LTerm_style has no faint/dim attribute; approximate dim with gray. *)
    | "debug" | "dim" -> { none with foreground = Some lblack }
    | "bold" -> { none with bold = Some true }
    | _ -> none

  type kind_style = { prefix : string; tag : string option }

  let style_for : Display.Info.kind option -> kind_style =
    let open Display.Info in
    function
    | Some Error -> { prefix = "error: "; tag = Some "error" }
    | Some Warning -> { prefix = "warning: "; tag = Some "warning" }
    | Some Response -> { prefix = "=> "; tag = Some "response" }
    | Some Debug -> { prefix = "debug: "; tag = Some "debug" }
    | Some Info | None -> { prefix = ""; tag = None }

  (* Map the frontend-agnostic [Display.Info] styling vocabulary onto LTerm's. *)
  let color_to_lterm : Display.Info.color -> LTerm_style.color =
    let open LTerm_style in
    function
    | Black -> black
    | Red -> red
    | Green -> green
    | Yellow -> yellow
    | Blue -> blue
    | Magenta -> magenta
    | Cyan -> cyan
    | White -> white
    | Bright_black -> lblack
    | Bright_red -> lred
    | Bright_green -> lgreen
    | Bright_yellow -> lyellow
    | Bright_blue -> lblue
    | Bright_magenta -> lmagenta
    | Bright_cyan -> lcyan
    | Bright_white -> lwhite
    | Rgb (r, g, b) -> rgb r g b

  let style_to_lterm (s : Display.Info.style) : LTerm_style.t =
    {
      LTerm_style.none with
      bold = (if s.bold then Some true else None);
      underline = (if s.underline then Some true else None);
      foreground = Option.map color_to_lterm s.foreground;
      background = Option.map color_to_lterm s.background;
    }

  (* Render a [kind] prefix ("error: ", "=> ", ...) as a styled fragment. *)
  let render_prefix ~use_color (prefix : string) (tag : string option) :
      LTerm_text.t =
    if prefix = "" then [||]
    else
      let sty =
        match tag with
        | Some t when use_color -> color_of_tag t
        | _ -> LTerm_style.none
      in
      LTerm_text.stylise prefix sty

  (* A [Fmt] body: run the thunk through a styled formatter so any embedded
     [@{<..>@}] semantic tags become styles. *)
  let render_fmt ~use_color (form : Display.form) : LTerm_text.t =
    let read_color = if use_color then Some color_of_tag else None in
    let get_content, ppf = LTerm_text.make_formatter ?read_color () in
    Format.fprintf ppf "@[<v>%t@]" form;
    get_content () (* flushes the formatter *)

  (* A [Rich] body: pre-styled spans map directly to LTerm styled text. *)
  let render_rich ~use_color (spans : Display.Info.rich) : LTerm_text.t =
    Array.concat
      (List.map
         (fun (sp : Display.Info.span) ->
           let sty =
             if use_color then style_to_lterm sp.style else LTerm_style.none
           in
           LTerm_text.stylise sp.text sty)
         spans)

  let render_msg (m : Display.Info.t) : unit Lwt.t =
    let open Lwt.Syntax in
    let { prefix; tag } = style_for m.kind in
    let use_color = M.use_color in
    let body =
      match m.msg with
      | Display.Info.Fmt form -> render_fmt ~use_color form
      | Display.Info.Rich spans -> render_rich ~use_color spans
    in
    let styled = Array.append (render_prefix ~use_color prefix tag) body in
    let* term' = term in
    LTerm.fprintls !term' styled

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
