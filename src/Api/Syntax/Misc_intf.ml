module type MISC = sig

  module Ast : Ast_intf.AST
  module Common : Common.COMMON
  open Common 
  (** {2 Explicit Substitutions}

      Substitutions map de Bruijn indices to {!front} values. The key
      primitives are the identity ([id]), shift ([shift]), and inverse
      shift ([invShift]), with composition and application operations. *)

  val id : Ast.sub
  (** Identity substitution {m \hat{{id}}} = [Shift 0].

      Invariant: {m \Gamma \vdash \mathrm{id} : \Gamma}. *)

  val shift : Ast.sub
  (** Shift substitution {m \uparrow} = [Shift 1]. Increments all de Bruijn
      indices by one, effectively weakening the context by one declaration.

      Invariant: {m \Gamma, V \vdash \uparrow : \Gamma}. *)

  val invShift : Ast.sub
  (** Inverse shift {m \uparrow^{{-1}}} = [Dot (Undef, id)]. Drops the most
      recently bound variable from scope.

      Invariant: {m \Gamma \vdash \uparrow^{{-1}} : \Gamma, V}. *)

  val bvarSub : int * Ast.sub -> Ast.front
  (** [bvarSub (n, s)] looks up the [n]-th position in substitution [s],
      returning the {!front} that index [n] maps to.

      Invariant: if {m \Gamma \vdash s : \Gamma'} and {m \Gamma' \vdash n : V}
      then [bvarSub (n, s)] = {m F} and {m \Gamma \vdash F : V[s]}. *)

  val frontSub : Ast.front * Ast.sub -> Ast.front
  (** [frontSub (Ft, s)] applies substitution [s] to front [Ft].

      Invariant: if {m \Gamma \vdash s : \Gamma'} and {m \Gamma' \vdash \mathit{Ft} : V}
      then [frontSub (Ft, s)] = {m \mathit{Ft}[s]} and {m \Gamma \vdash \mathit{Ft}[s] : V[s]}. *)

  val decSub : Ast.dec * Ast.sub -> Ast.dec
  (** [decSub (D, s)] applies substitution [s] to declaration [D].
      For [Dec (x, V)], returns [Dec (x, EClo (V, s))].
      For [BDec (n, (l, t))], composes the block substitution: [BDec (n, (l, comp (t, s)))].
      For [NDec x], returns unchanged. *)

  val blockSub : Ast.block * Ast.sub -> Ast.block
  (** [blockSub (B, s)] applies substitution [s] to block [B].

      Invariant: if {m \Gamma \vdash s : \Gamma'} and {m \Gamma' \vdash B\;\mathsf{block}}
      then {m \Gamma \vdash B[s]\;\mathsf{block}}. *)

  val comp : Ast.sub * Ast.sub -> Ast.sub
  (** [comp (s1, s2)] computes the composition {m s_1 \circ s_2}.

      Invariant: if {m \Gamma' \vdash s_1 : \Gamma} and {m \Gamma'' \vdash s_2 : \Gamma'}
      then {m \Gamma'' \vdash s_1 \circ s_2 : \Gamma}. *)

  val dot1 : Ast.sub -> Ast.sub
  (** [dot1 s] = [Dot (Idx 1, comp (s, shift))], the "dot-1" operation
      that extends [s] to work under one additional binder.

      Invariant: if {m \Gamma \vdash s : \Gamma'} then for all [V] such that
      {m \Gamma' \vdash V : L}, we have {m \Gamma, V[s] \vdash \mathrm{dot1}(s) : \Gamma', V}.

      Optimization: [dot1 (Shift 0)] = [Shift 0]. *)

  val invDot1 : Ast.sub -> Ast.sub
  (** [invDot1 s] = [comp (comp (shift, s), invShift)], the inverse of {!dot1}.

      Invariant: [invDot1 (dot1 s)] = [s], i.e.,
      [invDot1 (Dot (Idx 1, s' o ^))] = [s']. *)

  (** {2 Existential Variable Construction} *)

  val newEVar : Ast.dctx * Ast.exp -> Ast.exp
  (** [newEVar (G, V)] creates a fresh uninstantiated existential variable
      {m X : \Gamma \vdash V} with an empty constraint list.
      Returns [EVar (ref None, G, V, ref \[\])]. *)

  val newAVar : unit -> Ast.exp
  (** [newAVar ()] creates a fresh assignable variable with no type, context,
      or constraint information. Returns [AVar (ref None)].
      Used for lightweight unification variables during reconstruction. *)

  val newTypeVar : Ast.dctx -> Ast.exp
  (** [newTypeVar G] creates a fresh existential variable of type [Type]
      in context [G]. Equivalent to [newEVar (G, Uni Type)].
      Used when a type must be inferred. *)

  val newLVar : Ast.sub * (Ast.cid * Ast.sub) -> Ast.block
  (** [newLVar (s, (l, t))] creates a fresh uninstantiated block logic variable
      [LVar (ref None, s, (l, t))]. The substitution [s] is suspended, and
      [(l, t)] identifies the block type declaration. *)

  (** {2 Definition and Ancestor Functions} *)

  val headOpt : Ast.exp -> Ast.head option
  (** [headOpt U] extracts the head of expression [U] if it is in strict
      normal form (a {!Root} at the outermost level, possibly under lambdas
      or tags). Returns [None] for non-atomic forms.
      Does {e not} look through {!EClo} or {!EVar}. *)

  val ancestor : Ast.exp -> Ast.ancestor
  (** [ancestor U] computes ancestor information for an expression [U],
      used in termination checking for definitions [d = U : A]. *)

  val defAncestor : Ast.cid -> Ast.ancestor
  (** [defAncestor d] retrieves the stored ancestor information for
      defined constant [d].
      @raise Match_failure if [d] is not a {!ConDef}. *)

  (** {2 Target Type Family Functions}

      These functions extract the head constant of the target (return) type
      of a type expression, looking through Pi-types, redexes, closures, and tags. *)

  val targetHeadOpt : Ast.exp -> Ast.head option
  (** [targetHeadOpt V] returns the head of the atomic target type of [V],
      or [None] if [V] is a kind, an object, or has a variable type.
      Does {e not} expand type definitions ({!Def}). *)

  val targetHead : Ast.exp -> Ast.head
  (** [targetHead V] extracts the head of the atomic target type of [V].
      Like {!targetHeadOpt} but assumes [V] is a valid type with an atomic target.
      @raise Invalid_argument if [targetHeadOpt V] returns [None]. *)

  val targetFamOpt : Ast.exp -> Ast.cid option
  (** [targetFamOpt V] returns the {!cid} of the type family at the atomic
      target of [V], or [None]. Unlike {!targetHeadOpt}, this {e does}
      expand type definitions (following {!Def} to its definition). *)

  val targetFam : Ast.exp -> Ast.cid
  (** [targetFam V] extracts the type family {!cid} of the atomic target of [V].
      Like {!targetFamOpt} but assumes [V] is a valid type with a constant target.
      @raise Invalid_argument if [targetFamOpt V] returns [None]. *)

  val rename : Ast.cid * string -> unit
  (** [rename (c, name)] changes the name of constant [c] in the global
      signature to [name], preserving all other fields. Used by the Flit
      module for name mangling. *)

end
