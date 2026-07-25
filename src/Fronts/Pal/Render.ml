(** Renders {!Reply} values through the [Display] bus.

    This module is the printing seam between the value-returning pipeline
    ([Impl]) and the message-based frontends: library consumers work with
    {!Reply.outcome} directly and never call this, while the CLI and TUI push
    replies through here to get the classic Twelf-style output. *)

let reply : Reply.t -> unit = function
  | Reply.Installed _ ->
      (* Plain declarations are echoed (if at all) by the chatter-gated
         legacy layer, not here — matches historic behavior. *)
      ()
  | Reply.Decl condec ->
      Display.message ~level:Display.Level.normal ~kind:Display.Response
        (Display.Form.string (Print.Print_.conDecToString condec ^ "\n"))
  | Reply.Response s ->
      Display.message ~level:Display.Level.normal ~kind:Display.Response
        (Display.Form.string s)
  | Reply.Solutions _ ->
      (* Solution terms are still printed by the query engine itself. *)
      ()
  | Reply.Quit -> ()

let replies : Reply.t list -> unit = List.iter reply

let error (e : Reply.error) : unit =
  let stage_str =
    match e.stage with
    | Error.Error.Lex -> "lex"
    | Error.Error.Parse -> "parse"
    | Error.Error.Check -> "check"
    | Error.Error.Total -> "total"
    | Error.Error.Recon -> "recon"
    | Error.Error.Unknown -> "error"
    | Error.Error.Other s -> s
  in

  Display.message ~level:Display.Level.normal ~kind:Display.Error
    (Display.Form.string
       ("[" ^ stage_str ^ "] " ^ Display.Form.to_plain e.message))

(** Render everything an outcome carries and collapse it to the legacy exit
    status. *)
let report (o : Reply.outcome) : Loader.status =
  replies o.replies;
  match o.error with
  | None -> Loader.Ok
  | Some e ->
      error e;
      Loader.Abort
