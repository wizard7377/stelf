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

module Level : sig
  val quiet : level
  val terse : level
  val normal : level
  val verbose : level
  val debug : level
end

type form = Format.formatter -> unit

(* Bridges the untouched legacy 0-9 [Global.chatter] scale (default 3) used by
   old-style ported modules into the new -2..2 scale. *)
val from_chatter : int -> level

(* Inverse of [from_chatter], for pushing the new scale back into
   [Global.chatter] at CLI/frontend boundaries. *)
val to_chatter : level -> int

(* Frontend-agnostic styled text.  A message body is either a [Format] thunk
   ([Fmt]) or pre-styled rich text ([Rich]); terminal frontends render [Rich]
   richly while others flatten it via {!body_to_form}.  Deliberately
   lambda-term-free so non-terminal frontends don't link a terminal library. *)
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

val default_style : style

val span :
  ?bold:bool -> ?underline:bool -> ?fg:color -> ?bg:color -> string -> span
(** Build a styled span. *)

val plain : string -> span
(** Build an unstyled span. *)

val body_to_form : body -> form
(** Flatten any body to a plain-text [Format] thunk (drops styling). *)

val msg : ?src:src -> ?kind:kind -> ?level:level -> form -> t
val rich_msg : ?src:src -> ?kind:kind -> ?level:level -> rich -> t
