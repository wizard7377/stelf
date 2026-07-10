(** {1 Display Handlers}

    This is the display handling library, which handles queued messages and
    their display Note that this does not handle the actual formatting of the
    messages, but rather the message queue *)

module type DISPLAY = DISPLAY.DISPLAY

open Lwt.Syntax
include Info

module Display : DISPLAY = struct
  type t = Info.t

  let registered : bool ref = ref false
  let rep : (t -> unit Lwt.t) ref = ref (fun _ -> Lwt.return ())
  let fallback_verbosity : Info.level ref = ref Info.Level.normal
  let lock = Lwt_mutex.create ()

  let register f =
    registered := true;
    rep := f

  let set_fallback_verbosity v = fallback_verbosity := v

  let display' info =
    if not !registered then ()
    else
      Lwt.dont_wait
        (fun () -> Lwt_mutex.with_lock lock (fun () -> !rep info))
        (fun exn ->
          Printf.eprintf "Error in display handler: %s\n%!"
            (Printexc.to_string exn))

  let emit ?src ?kind ?(level = Info.Level.terse) (body : Info.body) =
    if not !registered then
      begin if !fallback_verbosity >= level then
        Printf.eprintf "%s\n%!" (Format.asprintf "%t" (Info.body_to_form body))
      end
    else
      Lwt.dont_wait
        (fun () ->
          Lwt_mutex.with_lock lock (fun () ->
              !rep { src; kind; level; msg = body }))
        (fun exn ->
          Printf.eprintf "Error in display handler: %s\n%!"
            (Printexc.to_string exn))

  let message ?src ?kind ?level t = emit ?src ?kind ?level (Info.Fmt t)
  let rich ?src ?kind ?level r = emit ?src ?kind ?level (Info.Rich r)
  let chatter ?src ?kind n t = message ?src ?kind ~level:(Info.from_chatter n) t

  let chatter_s ?src ?kind n s =
    chatter ?src ?kind n (fun ppf -> Format.pp_print_string ppf s)

  let debug ?src ?level t = message ?src ~kind:Info.Debug ?level t
  let info ?src ?level t = message ?src ~kind:Info.Info ?level t
  let warning ?src ?level t = message ?src ~kind:Info.Warning ?level t
  let error ?src ?level t = message ?src ~kind:Info.Error ?level t
  let response ?src ?level t = message ?src ~kind:Info.Response ?level t
end

module Info = Info
include Display

(* Compat shim: these functions re-implement the old Form.t API as plain
   Format.formatter → unit closures. Prefer Format/Fmt directly in new code.
   Access via Display.Form.* emits a deprecation alert. *)

let string s ppf = Format.pp_print_string ppf s
let empty _ppf = ()

let ( +++ ) a b ppf =
  a ppf;
  b ppf

let ( ++ ) a b ppf =
  a ppf;
  Format.pp_print_char ppf ' ';
  b ppf

let nl ?(n = 1) () ppf =
  for _ = 1 to n do
    Format.pp_print_newline ppf ()
  done

let space ?(n = 1) () ppf =
  for _ = 1 to n do
    Format.pp_print_char ppf ' '
  done

let shown f x ppf = Format.pp_print_string ppf (f x)

let concat ?(sep = empty) xs ppf =
  let first = ref true in
  List.iter
    (fun x ->
      if !first then first := false else sep ppf;
      x ppf)
    xs

let each ?(sep = empty) f xs = concat ~sep (List.map f xs)

let inside (l, r) x ppf =
  l ppf;
  x ppf;
  r ppf

let optional ?def f = function
  | None -> ( match def with Some d -> d | None -> empty)
  | Some x -> f x

let to_plain t = Format.asprintf "%t" t
let fmt ppf t = t ppf
let style f x = f x
let styles fs x = List.fold_left (fun acc f -> style f acc) x fs
let hbox xs ppf = List.iter (fun x -> x ppf) xs

let vbox xs ppf =
  let first = ref true in
  List.iter
    (fun x ->
      if !first then first := false else Format.pp_print_newline ppf ();
      x ppf)
    xs

let hvbox xs ppf = List.iter (fun x -> x ppf) xs

(** Compat re-export as Display.Form.* — deprecated, use Format/Fmt directly *)
module Form = struct
  let string = string
  let empty = empty
  let ( +++ ) = ( +++ )
  let ( ++ ) = ( ++ )
  let nl = nl
  let space = space
  let shown = shown
  let concat = concat
  let each = each
  let inside = inside
  let optional = optional
  let to_plain = to_plain
  let fmt = fmt
  let style = style
  let styles = styles
  let hbox = hbox
  let vbox = vbox
  let hvbox = hvbox

  module Style = struct
    let bold x = x
    let italic x = x
    let underline x = x

    module Fore = struct
      let black x = x
      let red x = x
      let green x = x
      let yellow x = x
      let blue x = x
      let magenta x = x
      let cyan x = x
      let white x = x
      let orange x = x
      let rgb _ _ _ x = x
    end

    module Back = struct
      let black x = x
      let red x = x
      let green x = x
      let yellow x = x
      let blue x = x
      let magenta x = x
      let cyan x = x
      let white x = x
      let orange x = x
      let rgb _ _ _ x = x
    end
  end

  module Syntax = struct
    let syntax x = x
  end
end

(* Also expose Style at the top level of Display for existing open-based call sites *)
module Style = Form.Style
