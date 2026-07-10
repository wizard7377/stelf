open Base
(** Lens based interface to CST

    Rather than having just one CST, STELF has a view based interface for the
    CST, allowing for new concrete syntax to be used without replacing any code
*)

module type S = sig
  type t
  type u

  val view : t -> u
  (** Unwrap "one layer" of the interface (ie, destruct) *)

  val review : u -> t
  (** Wrap "one layer" of the interface (ie, construct) *)
end

(** A lens is a pair of types, [t] and [u], with operations to convert between
    them In general, the following things should be true
    - [view] should be a left inverse to [review], i.e. [view (review x) = x]
      for all [x : u] (but they need not be right inverses)
    - [t] {e should not} be exposed
    - [u] {e should} be exposed
    - [t] should not mention [u]
    - [u] {e should} reference [t]
    - [u] should not reference itself

    These operations combined allow us to acheive lenses (actually, [u] should
    be complete and thus actually like a prism)

    In general, this should be used as [LENS with type t := t and type u := u]
*)
module type LENS = sig
  type t
  (** The concrete type we abstract over, should not be exposed *)

  type u
  (** The abstract type we almost always {e must} expose*)

  (** @inline *)
  include S with type t := t and type u := u

  val ( !> ) : t -> u
  (** Infix version of [view] *)

  val ( !< ) : u -> t
  (** Infix version of [review] *)
end

(** {2 LENS} *)

module type VIEW = sig
  exception Lacking
  (** Raised when a view case is not implemented for a given CST variant. *)

  module Paths : Paths.PATHS.PATHS
  (** Module of paths and regions, which we allow to be shared *)

  (** Abstract syntax tree type. (for internals) *)

  type loc
  (** Source location carried by CST nodes. *)

  type name = string
  (** Unqualified identifier. *)

  type namespace = string list
  (** Qualified namespace path. *)

  type symbol = namespace * name
  (** Qualified symbol as [(namespace, name)]. *)

  val mk_loc : int -> int -> loc
  (** Create a location from start and end lexer positions. *)

  val loc_to_region : loc -> Paths.region
  (** Convert a source location to a Paths region. *)

  val ghost : loc
  (** Synthetic location used for generated nodes. *)

  module Loc : sig
    type t

    type u =
      | Loc of Fpath.t option * int * int
          (** An actual location, with path, start, end. *)
      | Ghost  (** Synthetic location used for generated nodes. *)

    include LENS with type t := t and type u := u
  end

  (** {3 Term Syntax} *)
  module rec Term : sig
    type t

    type u =
      | Lowercase of Loc.t * symbol  (** A lowercase identifier in scope. *)
      | Uppercase of Loc.t * symbol  (** An uppercase identifier in scope. *)
      | Qualified of Loc.t * symbol
          (** An explicitly qualified identifier (eg, [%val (x y)]). *)
      | Text of Loc.t * string  (** A literal string (currently unused). *)
      | ExistVar of Loc.t * string
          (** An explicitly existential variable, you're probably looking for
              {!Uppercase}. *)
      | FreeVar of Loc.t * string
          (** A free variable, you're probably looking for {!Lowercase}. *)
      | Pi of Loc.t * Decl.t list * t
          (** A {m \Pi} type, which takes in a number of possible contexts. *)
      | Lam of Loc.t * Decl.t list * t
          (** Lambda abstraction binding declarations over a body. *)
      | App of Loc.t * t * t list
          (** Application of a head term to a spine of arguments. *)
      | HasType of Loc.t * t * t  (** Type ascription [{e term} : {e type}]. *)
      | Omitted of Loc.t  (** Implicit/omitted argument to be inferred. *)
      | Typ of Loc.t  (** The universe [type]. *)
      | Arrow of Loc.t * t * t  (** Non-dependent function type [A -> B]. *)
      | BackArrow of Loc.t * t * t  (** Reverse-direction arrow [B <- A]. *)
      | Foreign of Loc.t * t  (** Foreign/external term from an FFI. *)
      | Internal of int  (** Internal de Bruijn reference (not user-facing). *)
      | MacroParam of Loc.t * int option * int
          (** Macro parameter reference with optional binding level and index.
          *)
      | Local of Loc.t * namespace * t
          (** A local scope, similar to [N.(...)] in OCaml *)

    include LENS with type t := t and type u := u
  end

  (** Binder declaration constructors. *)
  and Decl : sig
    type t

    type u =
      | Decl1 of Loc.t * string option list * Term.t * Term.t
          (** Named binder with names, type, and optional body. *)
      | Decl0 of Loc.t * string option list * Term.t
          (** Binder with names and type only (no body position). *)

    include LENS with type t := t and type u := u
  end

  (** Top-level declaration constructors. *)
  module ConDec : sig
    type t

    type u =
      | ConstantDecl of Loc.t * Decl.t  (** Constant type declaration. *)
      | BlockDecl of Loc.t * string * Decl.t list * Decl.t list
          (** Block (world) declaration with universal and existential parts. *)
      | BlockDef of Loc.t * string * symbol list
          (** Block definition as a list of existing blocks. *)
      | ConstantDef of Loc.t * string * Term.t * Term.t option
          (** Constant definition with a body term and optional type annotation.
          *)

    include LENS with type t := t and type u := u
  end

  (** Mode syntax constructors. *)
  module Mode : sig
    type t

    type u =
      | Plus of Loc.t  (** Input mode ([+]). *)
      | Star of Loc.t  (** Unrestricted mode ([*]). *)
      | Minus of Loc.t  (** Output mode ([-]). *)
      | Minus1 of Loc.t  (** Unique output mode ([-1]). *)

    include LENS with type t := t and type u := u

    type t_mode := t

    (** Mode spine: sequence of mode annotations applied to a type family. *)
    module Spine : sig
      type t

      type u =
        | ModeNil of Loc.t  (** Empty mode spine. *)
        | ModeApp of Loc.t * (t_mode * string option) * t
            (** Mode spine cons: one mode annotation followed by the rest. *)

      include LENS with type t := t and type u := u
    end

    (** Mode term: a type family head annotated with a mode spine. *)
    module Term : sig
      type t

      type u =
        | ModeTerm of Loc.t * symbol * Spine.t
            (** Mode annotation on a named type family. *)
        | ModePi of Loc.t * Decl.t * t * t
            (** Pi-abstraction in a mode term. *)

      include LENS with type t := t and type u := u
    end

    (** Mode declaration: associates modes with a type family's arguments. *)
    module Dec : sig
      type t

      type u =
        | ModeDec of Loc.t * (t_mode * string option) list * Term.t
            (** A mode declaration binding a list of mode/name pairs to a type
                family. *)

      include LENS with type t := t and type u := u
    end
  end

  (** Module/signature syntax constructors. *)
  module Struct : sig
    (** Structure expression: reference to a named structure. *)
    module StrExp : sig
      type t

      type u =
        | StrExp of Loc.t * symbol
            (** Reference to a structure by qualified name. *)

      include LENS with type t := t and type u := u
    end

    (** Instantiation in a [where] clause. *)
    module Inst : sig
      type t

      type u =
        | ConInst of Loc.t * symbol * Loc.t * Term.t
            (** Constant instantiation in a [where] clause. *)
        | StrInst of Loc.t * symbol * Loc.t * StrExp.t
            (** Structure instantiation in a [where] clause. *)

      include LENS with type t := t and type u := u
    end

    (** Signature expression for module typing. *)
    module SigExp : sig
      type t

      type u =
        | Thesig of Loc.t  (** Anonymous signature ([the]). *)
        | SigId of Loc.t * string  (** Named signature reference. *)
        | WhereSig of Loc.t * t * Inst.t list
            (** Signature with [where]-clause instantiations. *)

      include LENS with type t := t and type u := u
    end

    (** Signature definition binding a name to a signature expression. *)
    module SigDef : sig
      type t

      type u =
        | SigDef of Loc.t * string option * SigExp.t
            (** A named (or anonymous) signature definition. *)

      include LENS with type t := t and type u := u
    end

    (** Structure declaration or definition. *)
    module StructDec : sig
      type t

      type u =
        | StructDecl of Loc.t * string option * SigExp.t
            (** Structure declaration with a signature ascription. *)
        | StructDef of Loc.t * string option * StrExp.t
            (** Structure definition as an alias for another structure. *)

      include LENS with type t := t and type u := u
    end
  end

  (** Logic programming query. *)
  module Query : sig
    type t

    type u =
      | Query of Loc.t * string option * Term.t
          (** A query with optional result name and goal term. *)

    include LENS with type t := t and type u := u
  end

  (** Top-level definition. *)
  module Define : sig
    type t

    type u =
      | Define of Loc.t * string option * Term.t * Term.t option
          (** A definition with optional name, body term, and optional type. *)

    include LENS with type t := t and type u := u
  end

  (** Solve declaration. *)
  module Solve : sig
    type t

    type u =
      | Solve of Loc.t * string option * Term.t
          (** A solve directive with optional name and goal term. *)

    include LENS with type t := t and type u := u
  end

  (** Operator fixity declarations. *)
  module Fixity : sig
    type t

    type u =
      | Left of Loc.t  (** Left-associative infix. *)
      | Right of Loc.t  (** Right-associative infix. *)
      | Prefix of Loc.t  (** Prefix operator. *)
      | Postfix of Loc.t  (** Postfix operator. *)
      | Middle of Loc.t  (** Non-associative infix. *)
      | None of Loc.t  (** Non-associative (same as {!Middle}). *)

    include LENS with type t := t and type u := u
  end

  (** Block item: a single entry in a block declaration. *)
  module BlockItem : sig
    type t

    type u =
      | Any of Loc.t * Decl.t
          (** Existentially quantified block entry (written [{...}]). *)
      | All of Loc.t * Decl.t
          (** Universally quantified block entry (written [[...]]). *)

    include LENS with type t := t and type u := u
  end

  (** Theorem-related syntax for totality and termination checking. *)
  module Thm : sig
    type t

    (** Empty variant: theorem nodes are only constructed via sub-modules. *)
    type u = |

    (** Termination orderings. *)
    module Order : sig
      type t

      type u =
        | Varg of Loc.t * string list
            (** Variable argument position(s) in a termination order. *)
        | Lex of Loc.t * t list  (** Lexicographic ordering of sub-orders. *)
        | Simul of Loc.t * t list  (** Simultaneous ordering of sub-orders. *)

      include LENS with type t := t and type u := u
    end

    (** Call patterns for totality declarations. *)
    module CallPats : sig
      type t

      type u =
        | CallPats of (string * string option list * Loc.t) list
            (** List of (name, argument pattern, location) triples. *)

      include LENS with type t := t and type u := u
    end

    (** Termination declaration. *)
    module TDecl : sig
      type t

      type u =
        | TDecl of Order.t * CallPats.t
            (** Termination order paired with call patterns. *)

      include LENS with type t := t and type u := u
    end

    (** Predicate reference in a reduction declaration. *)
    module Predicate : sig
      type t

      type u =
        | Predicate of string * Loc.t
            (** Named predicate with source location. *)

      include LENS with type t := t and type u := u
    end

    (** Reduction declaration. *)
    module RDecl : sig
      type t

      type u =
        | RDecl of Predicate.t * Order.t * Order.t * CallPats.t
            (** Predicate with input order, output order, and call patterns. *)

      include LENS with type t := t and type u := u
    end

    (** Declaration that a predicate uses tabled evaluation. *)
    module TabledDecl : sig
      type t

      type u =
        | TabledDecl of string * Loc.t
            (** Tabled predicate name and source location. *)

      include LENS with type t := t and type u := u
    end

    (** Declaration to persist a predicate's memo table. *)
    module KeepTableDecl : sig
      type t

      type u =
        | KeepTableDecl of string * Loc.t
            (** Kept table predicate name and source location. *)

      include LENS with type t := t and type u := u
    end

    (** Prove directive with search depth and termination declaration. *)
    module Prove : sig
      type t

      type u =
        | Prove of int * TDecl.t
            (** Search depth bound and termination declaration. *)

      include LENS with type t := t and type u := u
    end

    (** Establish directive (like {!Prove} but for meta-theorems). *)
    module Establish : sig
      type t

      type u =
        | Establish of int * TDecl.t
            (** Search depth bound and termination declaration. *)

      include LENS with type t := t and type u := u
    end

    (** Assert directive checking call patterns. *)
    module Assert : sig
      type t
      type u = Assert of CallPats.t  (** Assertion over call patterns. *)

      include LENS with type t := t and type u := u
    end

    (** Declaration context for theorem quantifiers. *)
    module Decs : sig
      type t

      type u =
        | DecsNil of Loc.t  (** Empty declaration context. *)
        | DecsList of t * Decl.t list  (** Non-empty declaration context. *)

      include LENS with type t := t and type u := u
    end

    (** Theorem formula syntax. *)
    module Thm : sig
      type t

      type u =
        | Top of Loc.t  (** Trivially true theorem. *)
        | Exists of Loc.t * Decs.t * t  (** Existentially quantified theorem. *)
        | Forall of Loc.t * Decs.t * t  (** Universally quantified theorem. *)
        | ForallStar of Loc.t * Decs.t * t
            (** Star-universally quantified theorem. *)
        | ForallG of Loc.t * (Decs.t * Decs.t) list * t
            (** Generalized universal quantification over contexts. *)

      include LENS with type t := t and type u := u
    end

    include LENS with type t := t and type u := u

    (** Named theorem declaration. *)
    module ThmDec : sig
      type t

      type u =
        | ThmDec of string * Thm.t  (** Theorem name paired with its formula. *)

      include LENS with type t := t and type u := u
    end

    (** World declaration: block patterns and call patterns. *)
    module WDecl : sig
      type t

      type u =
        | WDecl of (string list * string) list * CallPats.t
            (** Block identifier patterns and call patterns. *)

      include LENS with type t := t and type u := u
    end
  end

  (** Top-level commands (directives and declarations). *)
  module Cmd : sig
    type t

    type u =
      | Query of Loc.t * int option * int option * int option * Query.t
          (** Execute a bounded logic programming query. *)
      | QueryTabled of Loc.t * int option * int option * int option * Query.t
          (** Execute a tabled logic programming query. *)
      | AdhocQuery of Loc.t * Query.t
          (** Quick unbounded query (REPL shorthand). *)
      | Unique of Loc.t * Term.t
          (** Assert uniqueness of solutions for a type family. *)
      | Mode of Loc.t * Mode.Dec.t  (** Mode declaration for a type family. *)
      | Define of Loc.t * Define.t  (** Top-level definition. *)
      | DeclCmd of Loc.t * Term.t
          (** Bare declaration (constant declaration from a term). *)
      | Inline of Loc.t * string * Term.t  (** Inline constant definition. *)
      | Symbol of Loc.t * string * string
          (** Associate a symbolic alias with an existing identifier. *)
      | Freeze of Loc.t * string list
          (** Freeze constants (prevent further clauses). *)
      | Thaw of Loc.t * string list  (** Thaw frozen constants. *)
      | Sort of Loc.t * string list * Decl.t list
          (** Declare a new sort (type-level constant). *)
      | Term of Loc.t * Decl.t  (** Declare a new term-level constant. *)
      | Block of Loc.t * string * BlockItem.t list
          (** Declare a block (world). *)
      | Union of Loc.t * string * string list
          (** Define a block as a union of existing blocks. *)
      | Worlds of Loc.t * string list * Term.t list
          (** World declaration for type families. *)
      | Deterministic of Loc.t * string list
          (** Mark type families as deterministic. *)
      | Eval of Loc.t * t list  (** Evaluate a sequence of sub-commands. *)
      | Prec of Loc.t * Fixity.t * int * string list
          (** Fixity/precedence declaration. *)
      | Solve of Loc.t * Solve.t  (** Solve directive. *)
      | Stop of Loc.t * unit  (** Stop processing. *)
      | ReplQuit of Loc.t * unit  (** REPL quit command. *)
      | ReplHelp of Loc.t * string option  (** REPL help command. *)
      | ReplGet of Loc.t * string  (** REPL get-setting command. *)
      | ReplSet of Loc.t * string * string  (** REPL set-setting command. *)
      | ReplVersion of Loc.t * unit  (** REPL version command. *)
      | Total of Loc.t * Thm.Order.t list * Term.t list
          (** Totality declaration. *)
      | Terminates of Loc.t * Thm.Order.t list * Term.t list
          (** Termination declaration. *)
      | Covers of Loc.t * Mode.Dec.t  (** Coverage declaration. *)
      | Name of Loc.t * string  (** Name preference declaration. *)
      | Reduces of Loc.t * string * Term.t list
          (** Reduction ordering declaration. *)
      | Macro of Loc.t * int * string * t
          (** Defines a macro, taking its location, number of params, name, and
              the body. *)
      | Seq of Loc.t * item list
          (** A sequence of commands, for use with the module system. *)
      | Require of Loc.t * string list
          (** Ensure that the given path is loaded. *)
      | Open of Loc.t * string list  (** Open a scope into the current scope. *)
      | Scope of Loc.t * string * t  (** Enter into a new scope. *)
      | Use of Loc.t * string list * Term.t list  (** Apply a macro. *)

    and item =
      | Outer of string  (** Raw text segment between commands. *)
      | Cmd of t  (** An embedded command. *)

    include LENS with type t := t and type u := u
  end
end
