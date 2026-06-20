(** {1 Display Handlers}

    This is the display handling library, which handles queued messages and
    their display Note that this does not handle the actual formatting of the
    messages, but rather the message queue *)

module type DISPLAY = DISPLAY.DISPLAY

open Lwt.Syntax
include Form
include Info

module Display : DISPLAY = struct
  type t = Info.t

  let registered : bool ref = ref false
  let rep : (t -> unit Lwt.t) ref = ref (fun _ -> Lwt.return ())

  let register f =
    registered := true;
    rep := f

  let display' info =
    assert !registered;
    Lwt.dont_wait
      (fun () -> !rep info)
      (fun exn ->
        Printf.eprintf "Error in display handler: %s\n%!"
          (Printexc.to_string exn))

  let message ?src ?kind ?(level = Terse) t =
    assert !registered;
    Lwt.dont_wait
      (fun () -> !rep { src; kind; level; msg = t })
      (fun exn ->
        Printf.eprintf "Error in display handler: %s\n%!"
          (Printexc.to_string exn))

  let chatter ?src ?kind n t = message ?src ?kind ~level:(Info.from_chatter n) t
  let chatter_s ?src ?kind n s = chatter ?src ?kind n (Form.string s)

  let debug ?src ?level t = message ?src ~kind:Info.Debug ?level t
  let info ?src ?level t = message ?src ~kind:Info.Info ?level t
  let warning ?src ?level t = message ?src ~kind:Info.Warning ?level t
  let error ?src ?level t = message ?src ~kind:Info.Error ?level t
end

module Info = Info
include Display
include Info.Form
