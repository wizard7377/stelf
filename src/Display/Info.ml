type src =
  | Approx
  | Check
  | Compile
  | Typecheck
  | Unify
  | Cover
  | Parse
  | Reduce
  | Meta
  | Pal
  | Default
  | Recon
  | Prove
  | Total

type kind = Debug | Info | Warning | Error | Response

(* Verbosity is a plain numeral scale: -2 = quiet, -1 = terse, 0 = normal
   (default), 1 = verbose, 2 = debug. Kept distinct from [kind] (a message's
   formatting category, e.g. [Debug]) so a level is never mistaken for a kind. *)
type level = int

module Level = struct
  let quiet = -2
  let terse = -1
  let normal = 0
  let verbose = 1
  let debug = 2
end

(* Bridges the untouched legacy 0-9 [Global.chatter] scale (default 3) used by
   old-style ported modules into the new -2..2 scale. *)
let from_chatter x =
  assert (x >= 0);
  match x with
  | 0 | 1 -> Level.quiet
  | 2 -> Level.terse
  | 3 -> Level.normal
  | 4 -> Level.verbose
  | _ -> Level.debug

(* Inverse of [from_chatter], for pushing the new scale back into
   [Global.chatter] at CLI/frontend boundaries. *)
let to_chatter = function
  | x when x <= Level.quiet -> 0
  | x when x = Level.terse -> 2
  | x when x = Level.normal -> 3
  | x when x = Level.verbose -> 4
  | _ -> 5

type form = Format.formatter -> unit

(* Frontend-agnostic styled text.  A message body is either a [Format] thunk
   ([Fmt], as always) or pre-styled rich text ([Rich]).  Terminal frontends
   render [Rich] with real colors/attributes; other frontends flatten it to
   plain text via [body_to_form].  This stays lambda-term-free on purpose, so
   the core, LSP, and plain CLI paths never link a terminal library. *)
type color =
  | Black
  | Red
  | Green
  | Yellow
  | Blue
  | Magenta
  | Cyan
  | White
  | Bright_black
  | Bright_red
  | Bright_green
  | Bright_yellow
  | Bright_blue
  | Bright_magenta
  | Bright_cyan
  | Bright_white
  | Rgb of int * int * int

type style = {
  bold : bool;
  underline : bool;
  foreground : color option;
  background : color option;
}

type span = { text : string; style : style }
type rich = span list
type body = Fmt of form | Rich of rich
type t = { src : src option; kind : kind option; level : level; msg : body }

let default_style =
  { bold = false; underline = false; foreground = None; background = None }

(* Build a styled span. *)
let span ?(bold = false) ?(underline = false) ?fg ?bg text =
  { text; style = { bold; underline; foreground = fg; background = bg } }

(* Build an unstyled span. *)
let plain text = { text; style = default_style }

(* Flatten any body to a plain-text [Format] thunk (drops styling). *)
let body_to_form : body -> form = function
  | Fmt f -> f
  | Rich spans ->
      fun ppf -> List.iter (fun s -> Format.pp_print_string ppf s.text) spans

let msg ?(src : src option) ?(kind : kind option) ?(level = Level.normal)
    (fmt : form) : t =
  { src; kind; level; msg = Fmt fmt }

let rich_msg ?(src : src option) ?(kind : kind option) ?(level = Level.normal)
    (r : rich) : t =
  { src; kind; level; msg = Rich r }
