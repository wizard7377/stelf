open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Table
open! Table.Table_
open! Msg
open! Msg.Msg_
open! Print
open! Print.Print_
open! Debug

(** Term reconstruction: elaborating external syntax into internal LF.

    Reconstruction is the bridge between what the user writes and what the rest
    of the system type-checks. It takes a {!Cst.term} — the concrete syntax tree
    produced by the parser, full of omitted types and unresolved names — and
    produces a fully elaborated {!Ast.exp}: implicit arguments inserted, omitted
    types inferred, every identifier resolved, and every subterm mapped back to
    the source region it came from.

    {2 The two passes}

    Reconstruction runs in two stages, and the split matters for understanding
    the error messages it produces.

    The {b approximate} pass works over a stripped-down term language in which
    dependency is erased and only the arrow skeleton and the universe level
    survive. Its job is to resolve every identifier, solve the level and coarse
    type variables, and replace each omitted hole with a fresh approximate
    metavariable. Because it cannot fail on dependency, a type error here is
    recorded as a mismatch node rather than aborting — which is what lets a
    single file report many errors instead of only the first.

    The {b exact} pass then turns that approximate skeleton into real internal
    syntax, running full higher-order pattern unification, inserting implicit
    arguments, and building the occurrence tree ({!Paths.occExp}) that lets a
    later error be pointed at the right piece of source text.

    {2 Errors are accumulated, not thrown}

    Reconstruction does not raise on the first type error. Each error increments
    a counter and prints one located message, aborting early only if the count
    passes an internal threshold (200). Callers therefore use a pair of calls
    around each declaration: {!resetErrors} before, {!checkErrors} after — the
    latter being the barrier that finally raises {!Error} if anything went
    wrong. Reconstructing without calling {!checkErrors} will silently yield a
    term built from erroneous input. *)

module type RECON_TERM = sig
  module M : S.S
  module Cst = M.Cst
  module Ast = M.Ast
  module Paths = M.Paths
  module Syntax = M.Syntax

  exception Error of string
  (** Raised by {!checkErrors} when reconstruction recorded any error, and
      directly on a fatal error. The payload is already location-wrapped. *)

  val resetErrors : string -> unit
  (** [resetErrors filename] zeroes the error counter and sets the filename used
      to prefix subsequent messages. Call once per declaration, before building
      and reconstructing its job.

      Note this does {i not} clear the pending trace list; see {!traceMode}. *)

  val checkErrors : Paths.region -> unit
  (** [checkErrors r] is the barrier that turns accumulated errors into a raise.
      If any error was recorded since the last {!resetErrors}, it raises
      {!Error} reporting the count, attributed to region [r]. Otherwise it is a
      no-op. Call immediately after {!recon}. *)

  (** When tracing is enabled, controls {i when} trace output is produced. This
      is not a verbosity setting: both modes emit the same events, but they
      differ in whether terms are shown before or after instantiation. *)
  type traceMode =
    | Progressive
        (** Emit each trace message as it happens. Terms print as they were at
            that moment, so unsolved metavariables appear as metavariables, and
            each unification equation is shown {i before} it is attempted —
            giving a live view of the unifier, including the steps that fail. *)
    | Omniscient
        (** Defer every trace message until the whole job has been elaborated.
            By then every metavariable has been solved, so terms print in their
            final instantiated form. Unification runs silently and reports only
            on failure. *)

  val trace : bool ref
  (** Master switch for reconstruction tracing. Off by default. *)

  val traceMode : traceMode ref
  (** How {!trace} output is emitted. Defaults to {!Omniscient}. *)

  type t
  (** A reconstruction job: a tree of terms to be elaborated together, so that
      metavariables can be shared across them.

      This is the {i unreconstructed} form. Its leaves are already internal
      terms rather than {!Cst.term} — the conversion happens in the smart
      constructors below, not in {!recon} — but they are unelaborated: omitted
      holes are still holes, identifiers are still unresolved, and no implicit
      arguments have been inserted. *)

  val jnothing : t
  (** The empty job. Unit for {!jand}. *)

  val jand : t -> t -> t
  (** [jand (j1, j2)] reconstructs [j1] and [j2] together, sharing metavariables
      between them. *)

  val jwithctx : Cst.decl Ast.ctx -> t -> t
  (** [jwithctx (g, j)] reconstructs [j] under the additional hypotheses [g],
      which are themselves reconstructed first. Used for the [some]/[pi] parts
      of a context block and for theorem quantifiers. *)

  val jterm : Cst.term -> t
  (** [jterm tm] reconstructs [tm] as an object, inferring its type. *)

  val jclass : Cst.term -> t
  (** [jclass tm] reconstructs [tm] as a classifier — a type or a kind —
      inferring which universe it inhabits. *)

  val jof : Cst.term -> Cst.term -> t
  (** [jof (tm, ty)] reconstructs [tm] checked {i against} the classifier [ty],
      which is itself reconstructed. This is the ascription form, and it gives
      better error messages than reconstructing the two separately. *)

  (** The result of reconstructing a {!t}. Mirrors the job structure one-to-one,
      with each leaf replaced by fully elaborated internal syntax paired with
      the occurrence tree recording where each subterm came from. *)
  type result =
    | JNothing
    | JAnd of result * result
    | JWithCtx of Ast.dec Ast.ctx * result
    | JTerm of (Ast.exp * Paths.occExp) * Ast.exp * Ast.uni
        (** [JTerm ((u, occ), v, l)] — object [u] of type [v] in universe [l].
        *)
    | JClass of (Ast.exp * Paths.occExp) * Ast.uni
        (** [JClass ((v, occ), l)] — classifier [v] inhabiting universe [l]. *)
    | JOf of (Ast.exp * Paths.occExp) * (Ast.exp * Paths.occExp) * Ast.uni
        (** [JOf ((u, occ1), (v, occ2), l)] — object [u] checked against
            classifier [v] in universe [l]. *)

  val recon : t -> result
  (** Reconstruct a job appearing in a {i declaration}.

      An uppercase identifier that resolves to nothing becomes a
      {b free variable}, to be abstracted into an implicit argument of the
      declaration being elaborated. This is what makes [nat : type. z : nat.]
      work with implicit quantification. *)

  val reconQuery : t -> result
  (** Reconstruct a job appearing in a {i query}.

      Identical to {!recon} except in the treatment of unresolved uppercase
      identifiers: here they become {b existential variables} to be solved by
      the prover and reported back to the user by name, rather than being
      abstracted away. That single distinction is the whole difference between
      the two functions. (An identifier prefixed [__] is treated as existential
      in either mode.) *)

  val termRegion : Cst.term -> Paths.region
  (** The source region spanned by a term, computed by joining the regions of
      its subterms. Used to anchor error messages. *)

  val decRegion : Cst.decl -> Paths.region
  (** The source region spanned by a declaration. *)

  val ctxRegion : Cst.decl Ast.ctx -> Paths.region option
  (** The source region spanned by a whole context, or [None] if it is empty.
      Used to locate the [some]/[pi] parts of a context block when reporting an
      error against the block as a whole. *)

  val internalInst : 'a -> 'b
  (** Instantiate a constant declaration where the instantiating right-hand side
      is an existing constant.

      {b Unimplemented — raises unconditionally.} *)

  val externalInst : 'a -> 'b
  (** Instantiate a constant declaration where the instantiating right-hand side
      is an unreconstructed {!Cst.term}.

      {b Unimplemented — raises unconditionally.} Together with {!internalInst}
      these are the two halves of [where]-style signature instantiation; their
      only callers are in [ReconModule.applyEqns], which is not currently
      reachable from the front end. *)
end
