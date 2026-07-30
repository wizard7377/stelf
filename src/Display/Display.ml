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

(* Whether Style.* below emits real SGR escapes. Defaults to false on purpose:
   escapes are only correct on a formatter that writes straight to a terminal,
   and this library cannot find that out for itself — src/Display/dune has no
   unix, and adding one would drag a terminal dependency into the core, the LSP
   and every test. So the frontend that owns the formatter decides.

   Two consumers must not turn it on:
   - src/Fronts/Tui/Repl.ml, which re-encodes styling as LTerm_style values and
     pipes forms through LTerm_text.make_formatter; a raw escape arriving there
     is just text, and would be drawn literally.
   - anything whose output is asserted byte for byte (test/STELF/*.t). *)
let use_color : bool ref = ref false
let set_color (b : bool) : unit = use_color := b

(* Escapes go out via [Format.pp_print_as ppf 0]: Format is told the token is 0
   columns wide, so it never counts toward the margin and boxes keep measuring
   only the visible characters. pp_print_as queues the token like any other, so
   ordering against the styled text — and against any later break or flush — is
   preserved.

   [off] is the specific reset for the attribute being set (SGR 22/23/24/39/49)
   rather than a blanket SGR 0, so nested styles compose: in
   [style Style.bold @@ style Style.Fore.red @@ x] the colour closing does not
   also drop the bold. *)
let sgr ?(off = "0") (code : string) (x : form) : form =
 fun ppf ->
  if !use_color then begin
    Format.pp_print_as ppf 0 ("\027[" ^ code ^ "m");
    x ppf;
    Format.pp_print_as ppf 0 ("\027[" ^ off ^ "m")
  end
  else x ppf

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

(* WARNING: pp_print_newline RESETS the pretty-printer (format.mli): it closes
   every open box and flushes the device. It is not a line break. Prefer
   Format.pp_force_newline in new code — this stays as-is only because the cram
   tests in test/STELF assert the current output byte for byte. See Logo.ml's
   [row_break] for the correct primitive. *)
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

(* Note: with [set_color true], a styled form flattens to a string that CONTAINS
   escapes. That is fine today — the only call sites are Render.ml and
   test/Pal/Common.ml, and no styled form reaches either — but do not feed a
   styled form to this: Grace then measures the result for layout, and would
   count the escape bytes as visible width. *)
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

  (* Real SGR escapes, gated on Display.use_color. Note these are monomorphic
     [form -> form] where the previous stubs ([let bold x = x]) were fully
     polymorphic; every call site passes a form, so that is not a restriction in
     practice, but it is where an unexpected type error would come from. *)
  module Style = struct
    let bold = sgr ~off:"22" "1"
    let italic = sgr ~off:"23" "3"
    let underline = sgr ~off:"24" "4"
    let clamp v = if v < 0 then 0 else if v > 255 then 255 else v

    module Fore = struct
      let off = "39"
      let black = sgr ~off "30"
      let red = sgr ~off "31"
      let green = sgr ~off "32"
      let yellow = sgr ~off "33"
      let blue = sgr ~off "34"
      let magenta = sgr ~off "35"
      let cyan = sgr ~off "36"
      let white = sgr ~off "37"

      (* No SGR code names orange; 256-colour index 214 is the usual stand-in. *)
      let orange = sgr ~off "38;5;214"

      let rgb r g b =
        sgr ~off (Printf.sprintf "38;2;%d;%d;%d" (clamp r) (clamp g) (clamp b))
    end

    module Back = struct
      let off = "49"
      let black = sgr ~off "40"
      let red = sgr ~off "41"
      let green = sgr ~off "42"
      let yellow = sgr ~off "43"
      let blue = sgr ~off "44"
      let magenta = sgr ~off "45"
      let cyan = sgr ~off "46"
      let white = sgr ~off "47"
      let orange = sgr ~off "48;5;214"

      let rgb r g b =
        sgr ~off (Printf.sprintf "48;2;%d;%d;%d" (clamp r) (clamp g) (clamp b))
    end
  end

  module Syntax = struct
    let syntax x = x
  end
end

(* Also expose Style at the top level of Display for existing open-based call sites *)
module Style = Form.Style
