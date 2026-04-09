(** {1 The Internal Syntax}

    The internal syntax of the LF logical framework. This module defines
    the core representation of LF terms, types, kinds, declarations,
    contexts, explicit substitutions, and the global signature.

    Types and terms share the same syntactic category ({!exp}), following
    the style of the Edinburgh Logical Framework where the distinction
    between terms and types is maintained by the type system rather than
    the grammar.

    @author Frank Pfenning
    @author Carsten Schuermann
    @author Roberto Virga
    @author Asher Frost *)

open! Basis


(** Abstract type for position/metadata tags attached to expressions. *)
module type TAG = sig
  type t 
end

(** The internal syntax module type.
    @canonical Lambda.Intsyn.INTSYN *)
module type AST = sig 
  module Common : Common.COMMON
  open Common
  (** Provides position and metadata tags for expressions. *)

  (** {2 Basic Types} *)

  type cid = Common.Cid.t [@@deriving eq, ord, show]
  (** Constant identifier. An index into the global signature array. *)

  type mid = Common.Mid.t [@@deriving eq, ord, show]
  (** Structure (module) identifier. An index into the global structure array. *)

  type csid = Common.Cid.t [@@deriving eq, ord, show]
  (** Constraint-solver module identifier. Indexes into the foreign operation tables. *)

  type nonrec fgnExp = exn
  (** Foreign expression representation. Uses OCaml's extensible [exn] type
      so that constraint solvers can define their own expression forms. *)

  exception UnexpectedFgnExp of fgnExp
  (** Raised by a constraint solver when passed a foreign expression
      belonging to a different solver. *)

  type nonrec fgnCnstr = exn
  (** Foreign constraint representation. Uses OCaml's extensible [exn] type
      so that constraint solvers can define their own constraint forms. *)

  exception UnexpectedFgnCnstr of fgnCnstr
  (** Raised by a constraint solver when passed a foreign constraint
      belonging to a different solver. *)

  (** {2 Contexts} *)

  (** Contexts are snoc-lists of declarations, commonly written {m \Gamma}.
      They grow to the right: [Decl (Decl (Null, D1), D2)] represents
      {m \circ, D_1, D_2} where [D2] is the most recently bound declaration. *)
  type 'a ctx =
    | Null  (** Empty context {m \circ}. *)
    | Decl of 'a ctx * 'a
        (** Context extended with a declaration: {m \Gamma, D}. *)

  val null_ : 'a ctx
  (** The empty context {m \circ}. Equivalent to [Null]. *)

  (** {3 Context Operations} *)

  val ctxPop : 'a ctx -> 'a ctx
  (** [ctxPop (Decl (G, D))] returns [G], removing the most recent declaration.
      @raise Match_failure if the context is [Null]. *)

  val ctxLookup : 'a ctx * int -> 'a
  (** [ctxLookup (G, k)] returns the [k]-th declaration from the right
      (1-indexed). For example, [ctxLookup (G, 1)] returns the most recently
      added declaration.
      @raise Match_failure if [k] exceeds the context length. *)

  val ctxLength : 'a ctx -> int
  (** [ctxLength G] returns the number of declarations in [G]. *)

  (** {2 Syntax} *)

  (** Dependency information for function types.
      Tracks whether the bound variable actually appears in the body,
      which affects printing (arrow {m A \to B} vs. Pi {m \Pi x{:}A.\, B})
      and reconstruction behavior. *)
  type depend =
    | No  (** Non-dependent: the bound variable does not occur in the body.
              Printed as {m A \to B}. *)
    | Maybe  (** Possibly dependent: not yet determined during reconstruction. *)
    | Meta  (** Definitely dependent: the bound variable occurs in the body.
                Printed as {m \Pi x{:}A.\, B} or [{m \{x:A\} B}]. *)
  [@@deriving eq, ord, show]

  (** Universes of LF. In LF, types classify terms and kinds classify types. *)
  type uni = Kind  (** The universe of types. *) | Type  (** The universe of terms (objects). *)
  [@@deriving eq, ord, show]

  (** LF expressions. Types and terms share the same syntactic category;
      the distinction is maintained by the type system.

      Grammar:
      {v
        U ::= L                       Uni(L)
            | Pi (D, P). V            Pi((D, P), V)
            | H @ S                   Root(H, S)
            | U @ S                   Redex(U, S)
            | lam D. U                Lam(D, U)
            | X<I> : G|-V, Cnstr      EVar(r, G, V, Cnstr)
            | U[s]                    EClo(U, s)
            | A<I>                    AVar(r)
            | n                       NVar(n)
            | (foreign)               FgnExp(csid, fe)
      v} *)
  type exp =
    | Uni of uni
    (** A universe: [Uni Kind] classifies types, [Uni Type] classifies terms. *)

    | Pi of (dec * depend) * exp
    (** {m \Pi x{:}A.\, B}, the dependent function type.
        The first component is a declaration ({!dec}) paired with dependency
        information ({!depend}). The second component is the result type [B]
        in which the bound variable may occur. *)

    | Root of head * spine
    (** Atomic term: a {!head} applied to a {!spine} of arguments.
        Heads are canonical forms (constants, bound variables, projections).
        This is the normal form for applications where the head is not a lambda.
        See {!Redex} for non-canonical applications. *)

    | Redex of exp * spine
    (** Non-canonical application: an arbitrary expression applied to a spine.
        Unlike {!Root}, the head may be a lambda or other non-atomic expression.
        Reduced to {!Root} form during weak head-normal form computation. *)

    | Lam of dec * exp
    (** Lambda abstraction {m \lambda x{:}A.\, U}. The declaration introduces the
        bound variable and its type; the body may refer to it via de Bruijn index. *)

    | EVar of exp option ref * dec ctx * exp * cnstr_ ref list ref
    (** Existential (logic) variable {m X : \Gamma \vdash V}.
        - The [ref] cell holds [None] while uninstantiated, [Some U] once solved.
        - The {!dec} {!ctx} is the context in which the variable is valid.
        - The {!exp} is the type of the variable.
        - The constraint list tracks delayed unification constraints that
          mention this variable. *)

    | EClo of exp * sub
    (** Explicit closure {m U[s]}: an expression with a pending substitution.
        Substitutions are applied lazily; {!EClo} defers the work until the
        expression is inspected (e.g., during weak head-normal form computation). *)

    | AVar of exp option ref
    (** Assignable variable: a lightweight unification variable that carries
        no type, context, or constraint information. Used during term
        reconstruction to represent variables produced as part of a constraint graph. *)

    | FgnExp of csid * fgnExp
    (** Foreign expression provided by an external constraint solver.
        The {!csid} identifies which solver owns this expression. Operations
        on it are dispatched through {!FgnExpStd}. *)

    | NVar of int
    (** Named/linear variable represented by a de Bruijn index.
        Used internally for fully-applied bound variables in certain
        specialized contexts (memo tables, subtree indexing). Distinct
        from the {!BVar} head constructor which appears inside {!Root}. *)

    | Tag of Tag.t * exp
    (** A tagged expression carrying position information and other metadata.
        Tags are transparent to equality and comparison (ignored by [deriving]).
        @since 2.0 *)

  [@@deriving eq, ord, show]

  (** Heads of atomic terms ({!Root}).

      Grammar:
      {v
        H ::= k           BVar(k)       bound variable
            | c           Const(c)      constant
            | #i(b)       Proj(b, i)    block projection
            | c#          Skonst(c)     skolem constant
            | d           Def(d)        defined constant (strict)
            | d           NSDef(d)      defined constant (non-strict)
            | F[s]        FVar(F, V, s) free variable
            | (foreign)   FgnConst(..)  foreign constant
      v} *)
  and head =
    | BVar of int
    (** Bound variable with de Bruijn index [k] (1-indexed). *)
    | Const of cid
    (** Declared constant [c], referring to a {!ConDec} in the signature. *)
    | Proj of block * int
    (** Block projection [#i(b)]: the [i]-th component of block [b]. *)
    | Skonst of cid
    (** Skolem constant [c#]: introduced during coverage checking and
        abstraction to represent universally quantified variables. *)
    | Def of cid
    (** Strict defined constant [d]: its definition is expanded eagerly
        during weak head-normal form computation. Refers to a {!ConDef}
        in the signature. *)
    | NSDef of cid
    (** Non-strict defined constant [d]: its definition is expanded lazily
        (only when needed for unification). *)
    | FVar of string * exp * sub
    (** Free variable [F[s]] with name, type, and suspended substitution.
        Used during parsing and reconstruction before abstraction closes
        over free variables. *)
    | FgnConst of csid * conDec
    (** Foreign constant provided by constraint solver {!csid}. Carries
        its own {!conDec} rather than referencing the signature. *)
  [@@deriving eq, ord, show]

  (** Spines: sequences of arguments applied to a head.

      Grammar:
      {v
        S ::= Nil           empty spine
            | U ; S         argument followed by rest
            | S[s]          spine with pending substitution
      v} *)
  and spine =
    | Nil  (** Empty spine: no arguments. *)
    | App of exp * spine
    (** Argument application: [App (U, S)] represents [U ; S]. *)
    | SClo of spine * sub
    (** Spine closure: a spine with a pending explicit substitution. *)

  (** Explicit substitutions.

      A substitution maps de Bruijn indices to {!front} values. They are
      represented as a spine of {!Dot} constructors terminated by a {!Shift}:

      {v
        s ::= ^n             Shift(n)      shift indices by n
            | Ft . s         Dot(Ft, s)    map index 1 to Ft, rest by s
      v}

      For example, [Dot (Exp U, Dot (Exp V, Shift 3))] represents the
      substitution {m 1 \mapsto U,\; 2 \mapsto V,\; k \mapsto k+1} for {m k \geq 3}.

      Invariant: if {m \Gamma' \vdash s : \Gamma} then applying [s] to an
      expression valid in {m \Gamma} yields one valid in {m \Gamma'}. *)
  and sub =
    | Shift of int
    (** [Shift n] adds [n] to every de Bruijn index. [Shift 0] is the
        identity substitution; [Shift 1] is the standard weakening shift. *)
    | Dot of front * sub
    (** [Dot (Ft, s)] maps index 1 to [Ft] and index [k+1] to [s(k)].
        This extends substitution [s] with a new binding for the
        most recently bound variable. *)

  (** Fronts: the values that substitutions map indices to.

      Grammar:
      {v
        Ft ::= k           Idx(k)     index (renaming)
             | U           Exp(U)     expression
             | U           Axp(U)     assignable expression
             | _x          Block(b)   block value
             | _           Undef      undefined (for weakening)
      v} *)
  and front =
    | Idx of int
    (** A de Bruijn index. Represents a renaming: the variable is mapped
        to another variable rather than to a term. *)
    | Exp of exp
    (** An expression to substitute in for the variable. *)
    | Axp of exp
    (** Assignable expression: like {!Exp} but marks the substituted term
        as assignable during unification. Historical; currently unused
        in the OCaml port. *)
    | Block of block
    (** A block value, used when substituting block variables. *)
    | Undef
    (** Undefined: marks a position where no valid substitution exists.
        Used in {!invShift} ([^-1]) and weakening substitutions where
        a variable is dropped from scope. *)

  (** Declarations in LF contexts.

      The same declaration forms are used for both hypothetical
      (context-level) and top-level judgements.

      Grammar:
      {v
        D ::= x:V          Dec(x, V)        typed declaration
            | v:l[s]        BDec(v, (l, s))  block declaration
            | v[^-d]        ADec(v, d)       approximate declaration
            | v             NDec(v)          name-only declaration
      v} *)
  and dec =
    | Dec of string option * exp
    (** Standard variable declaration [x : V] with an optional name and
        a type expression. This is the most common declaration form. *)
    | BDec of string option * (cid * sub)
    (** Block declaration [v : l[s]]. The variable [v] is declared to
        inhabit block type [l] (a {!cid} referencing a {!BlockDec} in the
        signature) under substitution [s]. Used when a context variable
        ranges over a particular block structure. *)
    | ADec of string option * int
    (** Approximate declaration [v[^{-d}]]. Used during abstraction where
        the full type is not yet known; the integer [d] records the depth
        (number of enclosing binders to shift past). *)
    | NDec of string option
    (** Name-only declaration with no type information. Used as a
        placeholder during reconstruction when only the variable name
        is known. *)

  (** Blocks: grouped variable declarations used in world checking and
      regular worlds.

      Grammar:
      {v
        b ::= v                  Bidx(v)              block index
            | L(l[^k], t)        LVar(r, s, (l, t))   block logic variable
            | U1, ..., Un        Inst([U1; ...; Un])   instantiated block
      v}

      Blocks represent structured groups of hypotheses that appear together.
      They are declared via [%block] and referenced in [%worlds] declarations. *)
  and block =
    | Bidx of int
    (** Block index: a de Bruijn index referencing a block variable
        in the current context. *)
    | LVar of block option ref * sub * (cid * sub)
    (** Block logic variable: an uninstantiated block variable.
        - The [ref] cell holds [None] while unsolved, [Some b] once instantiated.
        - The {!sub} is a suspended substitution.
        - The [(cid * sub)] pair references the block type declaration
          and its type substitution. *)
    | Inst of exp list
    (** Instantiated block: a concrete list of expressions representing
        the components of a fully resolved block. *)

  (** Constraints: delayed unification problems attached to existential variables.

      Grammar:
      {v
        Cnstr ::= solved               Solved
                | G |- (U1 == U2)       Eqn(G, U1, U2)
                | (foreign)             FgnCnstr(csid, fc)
      v} *)
  and cnstr_ =
    | Solved
    (** The constraint has been resolved. *)
    | Eqn of dec ctx * exp * exp
    (** An equality constraint: in context {m \Gamma}, expressions
        [U1] and [U2] must be equal. Delayed when one side contains
        an uninstantiated existential variable. *)
    | FgnCnstr of csid * fgnCnstr
    (** A foreign constraint managed by an external solver. *)

  (** Status of a constant, controlling how it behaves during evaluation
      and unification. *)
  and status =
    | Normal
    (** Inert constant: no special evaluation behavior. *)
    | Constraint of csid * (dec ctx * spine * int -> exp option)
    (** Constraint constant: when applied, invokes the given function to
        potentially reduce. The function receives the context, argument
        spine, and arity, returning [Some U] if the constraint can be
        simplified or [None] to block. *)
    | Foreign of csid * (spine -> exp)
    (** Foreign constant: fully handled by an external solver.
        The function eagerly evaluates the application to produce a result. *)

  (** Result of attempting foreign unification. *)
  and fgnUnify =
    | Succeed of fgnUnifyResidual list
    (** Unification succeeded, producing a (possibly empty) list of
        residual operations that must be performed. *)
    | Fail
    (** Unification failed: the terms are not unifiable. *)

  (** Residual operations produced by successful foreign unification.
      These are instructions for the main unification engine to carry out. *)
  and fgnUnifyResidual =
    | Assign of dec ctx * exp * exp * sub
    (** Assignment: perform {m \Gamma \vdash X = U[s]}, instantiating
        the existential variable. *)
    | Delay of exp * cnstr_ ref
    (** Delay: suspend a constraint, associating it with all rigid
        existential variables in the expression. The constraint will
        be re-awakened when those variables are instantiated. *)

  (** Constant declarations in the global signature.

      Each variant stores the constant's name, optional parent structure,
      and variant-specific data. These are stored in the signature array
      and retrieved by {!sgnLookup}. *)
  and conDec =
    | ConDec of string * mid option * int * status * exp * uni
    (** Typed constant declaration [a : V : L].
        Fields: name, parent structure, number of implicit arguments,
        status, type, and universe (Kind or Type). *)
    | ConDef of string * mid option * int * exp * exp * uni * ancestor
    (** Constant definition [d = U : V : L].
        Fields: name, parent, implicit args, {e definition body} [U],
        type [V], universe, and ancestor information for termination. *)
    | AbbrevDef of string * mid option * int * exp * exp * uni
    (** Abbreviation definition [a = U : V : L]. Like {!ConDef} but
        without ancestor tracking. Abbreviations are expanded non-strictly
        (only when needed) and do not participate in termination analysis.
        Fields: name, parent, implicit args, definition body, type, universe. *)
    | BlockDec of string * mid option * dec ctx * dec list
    (** Block declaration [%block l : SOME G PI D1 ... Dn].
        Fields: name, parent, the "some" context of parameters,
        and the list of "pi" declarations that form the block body. *)
    | BlockDef of string * mid option * cid list
    (** Block definition [%block l = (l1 | ... | ln)].
        A union of existing block declarations. Fields: name, parent,
        list of block declaration {!cid}s. *)
    | SkoDec of string * mid option * int * exp * uni
    (** Skolem constant declaration. Introduced during coverage checking
        to witness universal quantification. Fields: name, parent,
        implicit args, type, universe. *)

  (** Ancestor information for defined constants, used in termination checking.

      [Anc (head, height, deepHead)] where:
      - [head] is [Some c] if expanding the definition one step yields
        an atomic type headed by [c], or [None] if it yields a function type.
      - [height] is the number of expansion steps to reach a non-definition head.
      - [deepHead] is the head after full expansion ([height] steps). *)
  and ancestor = Anc of cid option * int * cid option

  (** Structure (module) declaration in the signature. *)
  type strDec = StrDec of string * mid option [@@deriving eq, ord, show]
  (** [StrDec (name, parent)] declares a structure with the given name
      and optional parent structure. *)

  (** How a constant declaration was introduced. *)
  type conDecForm =
    | FromCS  (** Introduced by a constraint solver. *)
    | Ordinary  (** Ordinary top-level declaration. *)
    | Clause  (** Introduced via a [%clause] declaration. *)
  [@@deriving eq, ord, show]

  type nonrec dctx = dec ctx
  (** Declaration context: a context of {!dec} entries. Alias for [dec ctx]. *)

  type nonrec eclo = exp * sub
  (** Expression closure: a pair {m (U, s)} representing {m U[s]}. *)

  type nonrec bclo = block * sub
  (** Block closure: a pair {m (B, s)} representing {m B[s]}. *)

  type nonrec cnstr = cnstr_ ref
  (** A mutable constraint reference. Constraints are shared via [ref] cells
      so that solving one updates all references. *)

  exception Error of string
  (** Raised when the global signature exceeds its maximum size. *)



  (** {2 Convenience Constructors} *)

  val arrow_ : exp * exp -> exp
  (** [arrow_ (A, B)] constructs the non-dependent function type
      {m A \to B}, i.e., [Pi ((Dec (None, A), No), B)]. *)

  (** {2 Constant Declaration Accessors} *)

  val conDecName : conDec -> string
  (** Extract the name of a constant declaration. *)

  val conDecParent : conDec -> mid option
  (** Extract the parent structure of a constant declaration. *)

  val conDecImp : conDec -> int
  (** Extract the number of implicit arguments. Returns [0] for {!BlockDec}
      and {!BlockDef}. *)

  val conDecStatus : conDec -> status
  (** Extract the status of a constant. Returns {!Normal} for all forms
      except {!ConDec}. *)

  val conDecType : conDec -> exp
  (** Extract the type of a constant declaration. Valid for {!ConDec},
      {!ConDef}, {!AbbrevDef}, and {!SkoDec}. *)

  val conDecBlock : conDec -> dctx * dec list
  (** Extract the "some" context and "pi" declaration list from a {!BlockDec}.
      @raise Match_failure if applied to a non-block declaration. *)

  val conDecUni : conDec -> uni
  (** Extract the universe ({!Kind} or {!Type}) of a constant declaration. *)

  (** {2 Structure Declaration Accessors} *)

  val strDecName : strDec -> string
  (** Extract the name of a structure declaration. *)

  val strDecParent : strDec -> mid option
  (** Extract the parent structure of a structure declaration. *)

end

