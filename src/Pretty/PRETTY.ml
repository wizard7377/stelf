(** Pretty-printing of the concrete syntax tree.

    This is the second half of term output. The first half, resugaring, turns
    internal syntax into a CST; this turns a CST into text. The two halves share
    no code and no state: everything this module needs that is not in the CST
    itself arrives through {!env}.

    All output is modern STELF surface syntax -- [{x A} B], [[x A] M],
    [%the A M] -- and, where the CST admits a surface form at all, parsing the
    output reproduces the input CST up to source locations. The exception is
    internal-tag nodes, which name parts of the internal syntax that have no
    surface form; those are deliberately unparseable. *)

(** Operator fixity, as the printer needs it.

    Deliberately {e not} [Names.Fixity]: the printer does not depend on the
    signature, so callers convert. [Names.Fixity.Strength n] maps to the [int]
    here unchanged. *)
module Fixity = struct
  type assoc = Left | Right | Non
  type t = Nonfix | Infix of int * assoc | Prefix of int | Postfix of int
end

type env = {
  fixity : string list * string -> Fixity.t;
      (** Declared fixity of a symbol, or [Nonfix] if it has none. *)
  margin : int;  (** Right margin, in columns, for line breaking. *)
}
(** Everything the printer needs that is not in the CST.

    [fixity] is a callback rather than a functor parameter because it varies per
    call, not per program: rendering against the live signature
    ([Names.fixityLookup]), against a parser-local table, and against nothing at
    all (tests, which want parenthesisation checked independently of whatever
    [%prec] declarations happen to be installed) all coexist in one process. *)

module type PRETTY = sig
  type term
  type decl
  type cmd

  exception Unsupported of string
  (** Raised by {!cmd} for command forms the printer does not render. Terms and
      declarations are total; commands are not. *)

  val term : env -> term -> Format.formatter -> unit
  (** Render a term in a slot where a full expression is allowed, so nothing is
      parenthesised at the outermost level. *)

  val decl : env -> decl -> Format.formatter -> unit
  (** Render a binder without its surrounding brackets, as [%term] takes it. *)

  val decls :
    env ->
    brackets:[ `None | `Braces | `Brackets ] ->
    decl list ->
    Format.formatter ->
    unit
  (** Render a sequence of binders, each wrapped in the given brackets. *)

  val cmd : env -> cmd -> Format.formatter -> unit
  (** Render a top-level command. Raises {!Unsupported} outside the forms
      resugaring produces. *)

  val term_to_string : env -> term -> string
  val decl_to_string : env -> decl -> string
  val cmd_to_string : env -> cmd -> string
end
