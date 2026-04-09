module type SGN = sig
  module Common : Common.COMMON
  module Ast : Ast_intf.AST with module Common = Common

  type cid = Ast.cid
  type mid = Ast.mid
  type conDec = Ast.conDec
  type strDec = Ast.strDec

  type dctx = Ast.dctx 
  class sgn : object
    (** {2 Global Signature Operations}

        The global signature is a mutable array mapping {!cid}s to {!conDec}s
        and {!mid}s to {!strDec}s. It represents the collection of all declared
        constants and structures. *)

    method sgnReset : unit -> unit
    (** Reset the global signature to empty, releasing all stored declarations.
        Resets both constant and structure counters to 0. *)

    method sgnSize : unit -> (int * int)
    (** [sgnSize ()] returns [(nextCid, nextMid)]: the number of constants and
        structures currently in the signature. *)

    method sgnAdd : conDec -> cid
    (** Add a constant declaration to the signature, returning its fresh {!cid}.
        @raise Error if the signature exceeds its maximum capacity. *)

    method sgnLookup : cid -> conDec
    (** Look up a constant declaration by its {!cid}. *)

    method sgnApp : (cid -> unit) -> unit
    (** [sgnApp f] applies [f] to every valid {!cid} in the signature, in order
        from 0 to [nextCid - 1]. *)

    method sgnStructAdd : strDec -> mid
    (** Add a structure declaration to the signature, returning its fresh
        {!mid}.
        @raise Error if the structure signature exceeds its maximum capacity. *)

    method sgnStructLookup : mid -> strDec
    (** Look up a structure declaration by its {!mid}. *)

    (** {2 Signature Convenience Lookups} *)

    method constType : cid -> Ast.exp
    (** [constType c] returns the type of constant [c]. Equivalent to
        [conDecType (sgnLookup c)]. *)

    method constDef : cid -> Ast.exp
    (** [constDef d] returns the definition body of defined constant [d]. Valid
        only for {!ConDef} and {!AbbrevDef} entries.
        @raise Match_failure if [d] is not a defined constant. *)

    method constImp : cid -> int
    (** [constImp c] returns the number of implicit arguments of constant [c].
        Equivalent to [conDecImp (sgnLookup c)]. *)

    method constStatus : cid -> Ast.status
    (** [constStatus c] returns the status of constant [c]. Returns {!Normal}
        for all forms except {!ConDec}. *)

    method constUni : cid -> Ast.uni
    (** [constUni c] returns the universe ({!Kind} or {!Type}) of constant [c].
    *)

    method constBlock : cid -> dctx * Ast.dec list
    (** [constBlock c] returns the block structure of constant [c]. Valid only
        for {!BlockDec} entries. *)


    end
    (* {2 Context Lookups} *)
val ctxDec : dctx * int -> Ast.dec
  (** [ctxDec (G, k)] looks up the [k]-th declaration (1-indexed from the right)
      in context [G], applying the appropriate shift substitution so the
      returned type is valid in [G].

      Invariant: if {m |\Gamma| \geq k} then {m \Gamma \vdash k : V}
      where [V] is the type in the returned declaration. *)

  val blockDec : dctx * Ast.block * int -> Ast.dec
  (** [blockDec (G, b, i)] returns the [i]-th declaration from the block
      [b] in context [G]. Looks up the block's signature declaration and
      applies the appropriate substitution for projections.

      Invariant: if {m \Gamma(b) = l[s]} and {m \Sigma(l) = \mathsf{SOME}\; G_1\; \mathsf{BLOCK}\; D_1 \ldots D_n}
      then [blockDec (G, b, i)] returns {m D_i[s']}. *)

    val sgn_ : sgn
    (** Shared signature instance used by the API layer. *)

    val sgnLookup : cid -> conDec
    (** Module-level shortcut for looking up a constant declaration in the live
            shared signature. *)

    val rename : cid * string -> unit
    (** Change the stored name of a constant while preserving its other fields. *)


end
