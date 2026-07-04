exception Interrupted
let () = Printexc.register_printer (function Interrupted -> Some "Interrupted" | _ -> None)

module Repl (M : REPL.S) : REPL.REPL = struct
  let () =
    Debug.setup_log
      ~level:
        (Debug.Level.log_level @@ Debug.Level.from_chatter
        @@ Display.Info.to_int M.verbosity)
      ()

  let msgs : Display.Info.t list ref = ref []

  let add_msg (m : Display.Info.t) =
    let r =
      if Display.Info.to_int M.verbosity >= Display.Info.to_int m.level then
        m :: !msgs
      else !msgs
    in
    msgs := r

  let flush_msgs () : Display.Info.t array Lwt.t =
    let pending = Array.of_list (List.rev !msgs) in
    msgs := [];
    Lwt.return pending

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
  
  let rec read : (string -> response Lwt.t) -> int Lwt.t =
   fun f ->
    let open Lwt.Syntax in
    let* term' = term in
    let pp_msg fmt m : unit = Grace_ansi_renderer.pp_diagnostic fmt m in
    let display_msg (s : Grace.Diagnostic.Severity.t) (m : Display.Info.t) : unit Lwt.t =
      let diag = Grace.Diagnostic.create s (fun ppf -> Display.fmt ppf m.msg) in
      let str = Format.asprintf "%a" pp_msg diag in
      LTerm.printf "%s" str in
    let open Grace.Diagnostic.Severity in
    let display_err (m : Display.Info.t) : unit Lwt.t =
      display_msg Error m
    in
    let display_warn (m : Display.Info.t) : unit Lwt.t =
      display_msg Warning m
    in
    let display_info (m : Display.Info.t) : unit Lwt.t =
      display_msg Note m
    in
    let display_debug (m : Display.Info.t) : unit Lwt.t =
      display_msg Note m
    in
    let display_response (m : Display.Info.t) : unit Lwt.t =
      let arrow = Notty.(I.string A.(fg (rgb_888 ~r:255 ~g:165 ~b:0) ++ st bold) "=>") in
      let msg_str = Format.asprintf "%t" m.msg in
      let msg_img = Notty.I.string Notty.A.empty (" " ^ msg_str) in
      Notty_lwt.output_image (Notty_lwt.eol Notty.I.(arrow <|> msg_img))
    in

    let should_display (msg : Display.Info.t) : bool =
      Display.Info.( >= ) M.verbosity msg.level
    in
    let display : Display.Info.t -> unit Lwt.t =
     fun m ->
      if should_display m then
        Display.Info.(
          match m.kind with
          | Some Error -> display_err m
          | Some Warning -> display_warn m
          | Some Info -> display_info m
          | Some Debug -> display_debug m
          | Some Response -> display_response m
          | None -> display_info m)
      else Lwt.return ()
    in
    let flush () : unit Lwt.t =
      begin
        let open Lwt.Syntax in
        let* pending = flush_msgs () in
        let pending_list = Array.to_list pending in
        Lwt_list.iter_s (fun info -> display info) pending_list
      end
    in
    let rec read_multiline (acc : string) : string Lwt.t =
      let prompt = if String.equal acc "" then "λΠ> " else "  > " in
      let* line = read_line !term' prompt in
      let full = if String.equal acc "" then line else acc ^ "\n" ^ line in
      if ends_with_terminator full || String.equal (String.trim full) ""
      then Lwt.return full
      else read_multiline full
    in
    Lwt.catch
      (fun () ->
        let* r0 = read_multiline "" in
        let* continue =
          try f r0 with
          | Sys.Break -> Lwt.return Stop
          | exn ->
              let x = Printexc.to_string exn in
              let* () =
                display_err (Display.Info.msg @@ Display.Form.string x)
              in
              Lwt.return Continue
        in

        match continue with
        | Continue ->
            let* () = flush () in
            read f
        | Fail msg ->
            Printf.eprintf "Error: %s\n%!" msg;
            let* () = flush () in
            Lwt.return 1
        | Stop ->
            let* () = flush () in
            Lwt.return 0)
      (fun exn ->
        match exn with
        | LTerm_read_line.Interrupt ->
            let* () = flush () in
            Lwt.return 0
        | exn ->
            let* () =
              display_err
                (Display.Info.msg @@ Display.Form.string
                @@ Printexc.to_string exn)
            in
            let* () = flush () in
            read f)

  let show fmt = () (* Format.pp_print_string fmt "λΠ> "*)
end
