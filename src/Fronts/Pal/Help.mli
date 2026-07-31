(** The catalogue of STELF's [%]-commands.

    Single source of truth for what the REPL's [%help] prints. There is one
    entry per alternative in the [choice] table of [src/Fronts/Modern/Cmd.ml],
    and the categories follow §6 of [hacking/grammar/stelf.md] — a command added
    to the parser must be added to both, and there is no mechanism that will
    notice if it isn't. (The parser keeps no keyword list to compare against;
    exporting one from [Cmd] is the real fix.)

    Deliberately absent: [Cst.Macro_], which [Impl] handles but the Modern
    parser has no alternative for, so it is unreachable. *)

type status =
  | Works  (** implemented *)
  | Caveat of string  (** implemented, with a condition worth stating *)
  | Stub of string  (** parses, then does nothing or fails *)

type entry = {
  name : string;  (** the keyword, without its leading [%] *)
  aliases : string list;
      (** other spellings the parser accepts for the same command, e.g. [define]
          for [def]; {!find} matches these too *)
  summary : string;  (** one line, no trailing period *)
  status : status;
}

type category = {
  title : string;  (** heading shown in the overview *)
  slug : string;  (** what [%help TOPIC] matches a whole category on *)
  entries : entry list;
}

val categories : category list

val entries : entry list
(** [categories] flattened, in declaration order. *)

val find : string -> entry option
(** Looks up a command by {!entry.name} or by any of its {!entry.aliases}. *)

val overview : string
(** What a bare [%help] prints: a categorised list of every command. *)

val topic : string -> string
(** What [%help TOPIC] prints, for a command name or a category slug. *)
