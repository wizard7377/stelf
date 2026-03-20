(** {1 The Internal Syntax}

@author Frank Pfenning
@author Carsten Schuermann
@author Roberto Virga
@author Asher Frost
*)

open! Basis
open Fgnopn

(** The internal syntax module type *)
module type INTSYN = sig

  (** {2 Basic Types} *)

  (** {3 Aliases and Exceptions} *)
  (** Constant identifier (alias for {!int}). *)
  type cid = int [@@deriving eq, ord, show]

  (** Structure identifier (alias for {!int}). *)
  type mid = int [@@deriving eq, ord, show]

  (** Constraint-solver module identifier. *)
  type csid = int [@@deriving eq, ord, show]

  (** foreign expression representation *)
  type nonrec fgnExp = exn

  (** Raised by a constraint solver when passed an incorrect foreign expression. *)
  exception UnexpectedFgnExp of fgnExp

  (** raised by a constraint solver
 					   if passed an incorrect arg *)
  (** foreign constraint representation *)
  type nonrec fgnCnstr = exn

  (** Raised by a constraint solver when passed an incorrect foreign constraint. *)
  exception UnexpectedFgnCnstr of fgnCnstr
  (** raised by a constraint solver
                                            if passed an incorrect arg *)


  (** {3 Contexts} *)
                                            
  (** Context (lists of statements), commonly {m \Gamma}. *)
  type 'a ctx = 
    | Null (** Empty context {m \circ} *) 
    | Decl of 'a ctx * 'a (** Context consed onto a statement {m \Gamma , \phi} *)


  val null_ : 'a ctx
    (** Empty context *)

  (** {4 Context Operations} *)

  (** Removes the last statement from the context *)
  val ctxPop : 'a ctx -> 'a ctx

  (** Looks up a statement in the context from its index *)
  val ctxLookup : 'a ctx * int -> 'a

  (** Returns the length of the context *)
  val ctxLength : 'a ctx -> int


  (** Dependency information for function types    *)
  type depend = 
    | No (** Non dependent function *)
    | Maybe (** Possibly dependent function *)
    | Meta (** Definitely dependent function. *)
    [@@deriving eq, ord, show]

  (** Sorts of LF *)
  type uni = 
    |  Kind 
    (** Kinds *)
    |  Type 
    (** Types *)

    [@@deriving eq, ord, show]
  (** 
      The type of LF expressions, {m e}. Types have the same syntax as terms. 
      *)
  type exp =
    | Uni of uni
    (** A value describing a universe {!uni} *)

    | Pi of (dec * depend) * exp
    (** 
        {m \Pi} types, dependent function types. 
        The first parameter of these describes the declaration being introduced, {!dec}.
        The second, {!depend}, models whether the function is simple or dependent 
        The final argument is the resulting type 
        *)

    | Root of head * spine
    (** Juxtaposition when the head is in normal form, for instance, {m add 5 4}. *)

    | Redex of exp * spine
    (** Juxtaposition where the head is not in normal form.
      See {!Root}. *)

    | Lam of dec * exp
    (** A lambda abstraction, with the declerations introduced and the resulting expression *)

    | EVar of exp option ref * dec ctx * exp * cnstr_ ref list ref
  (**     | X<I> : G|-V, Cnstr   *)

    | EClo of exp * sub
  (**     | U[s]                 *)

    | AVar of exp option ref
    (** [A<I>] *)

    | FgnExp of csid * fgnExp
  (**     | (foreign expression) *)

    | NVar of int
    (** Variable indexed *)
    [@@deriving eq, ord, show]

  (** Heads of clauses *)
  and head =
    | BVar of int
    (** Bound variable *)

    | Const of cid
    (** A free variable *)

    | Proj of block * int
  (**     | #k(b)                *)

    | Skonst of cid
  (**     | c#                   *)
    | Def of cid
  (**     | d (strict)           *)
    | NSDef of cid
  (**     | d (non strict)       *)
    | FVar of string * exp * sub
  (**     | F[s]                 *)
    | FgnConst of csid * conDec
  (**     | (foreign constant)   *)
    [@@deriving eq, ord, show]

  (** Spines.

      Grammar:
      {[
      S ::= Nil
          | U ; S
          | S[s]
      ]}
  *)
  and spine =
    | Nil
    | App of exp * spine
    | SClo of spine * sub

  (** Explicit substitutions.

      Grammar:
      {[
      s ::= ^n
          | Ft.s
      ]}
  *)
  and sub =
    | Shift of int
    | Dot of front * sub

  (** Fronts.

      Grammar:
      {[
      Ft ::= k
           | U
           | _x
           | _
      ]}
  *)
  and front =
    | Idx of int
    (** [k] *)
    | Exp of exp
    (** [U] *)
    | Axp of exp
    (** Alternate expression form used in substitutions. *)
    | Block of block
    (** [_x] *)
    | Undef
    (** [_] *)

  (** Declarations.

      Grammar:
      {[
      D ::= x:V
          | v:l[s]
          | v[^-d]
      ]}
  *)
  and dec =
    | Dec of string option * exp
    | BDec of string option * (cid * sub)
    | ADec of string option * int
    | NDec of string option

  (** Blocks.

      Grammar:
      {[
      b ::= v
          | L(l[^k],t)
          | U1, ..., Un
      ]}

      Historical note: one possible extension is to let projections count like
      substitutions (for example, by adding a closure-like block form), but this
      remains deferred.
  *)
  and block =
    | Bidx of int
    | LVar of block option ref * sub * (cid * sub)
    | Inst of exp list

  (** Constraints.

      Grammar:
      {[
      Cnstr ::= solved
              | G|-(U1 == U2)
              | (foreign)
      ]}
  *)
  and cnstr_ =
    | Solved
    | Eqn of dec ctx * exp * exp
    | FgnCnstr of csid * fgnCnstr

  (** Status of a constant:
      - [Normal]: inert
      - [Constraint]: acts as a constraint
      - [Foreign]: converted to foreign handling
  *)
  and status =
    | Normal
    | Constraint of csid * (dec ctx * spine * int -> exp option)
    | Foreign of csid * (spine -> exp)

  (** Result of foreign unification. *)
  and fgnUnify = Succeed of fgnUnifyResidual list | Fail

  (** Residual operations produced by foreign unification:
      - [Assign]: perform [G |- X = U [ss]]
      - [Delay]: delay a constraint, associating it with rigid EVars
  *)
  and fgnUnifyResidual =
    | Assign of dec ctx * exp * exp * sub
    | Delay of exp * cnstr_ ref

  and conDec =
    | ConDec of
        string
        * mid option
        * int
        * status
        * exp
        * uni
      (** [a : K : kind] or analogous typed constant declaration. *)
    | ConDef of string * mid option * int * exp * exp * uni * ancestor
      (** [d = M : A : type] or [a = A : K : kind]. *)
    | AbbrevDef of
        string
        * mid option
        * int
        * exp
        * exp
        * uni
      (** [a = A : K : kind] abbreviation-like definition. *)
    | BlockDec of
        string
        * mid option
        * dec ctx
        * dec list
      (** [%block l : SOME G1 PI G2]. *)
    | BlockDef of string * mid option * cid list
      (** [%block l = (l1 | ... | ln)]. *)
    | SkoDec of
        string * mid option * int * exp * uni
      (** [sa : K : kind] skolem-like declaration. *)

  (** Ancestor information for [d] or [a]:
      [head(expand(d)), height, head(expand[height](d))].
      [None] means expansion yields [{x:A}B].
  *)
  and ancestor = Anc of cid option * int * cid option

  (** Structure declaration      *)
  type strDec = StrDec of string * mid option [@@deriving eq, ord, show]

  (** Form of constant declaration *)
  (** from constraint domain *)
  (** ordinary declaration *)
  (** %clause declaration *)
  type conDecForm = FromCS | Ordinary | Clause [@@deriving eq, ord, show]

  (** Type abbreviations *)
  (** G = . | G,D                *)
  type nonrec dctx = dec ctx

  (** Us = U[s]                  *)
  type nonrec eclo = exp * sub

  (** {m Bs = B_s m}                  *)
  type nonrec bclo = block * sub

  (** constraints *)
  type nonrec cnstr = cnstr_ ref

  exception Error of string

  (** Raised if out of space. *)
  (** Standard operations on foreign expressions. *)
  module FgnExpStd : sig
    (** Convert to internal syntax. *)
    module ToInternal : FGN_OPN with type arg = unit and type result = exp

    (** Apply a function to subterms. *)
    module Map : FGN_OPN with type arg = exp -> exp and type result = exp

    (** Apply a function to subterms for effect. *)
    module App : FGN_OPN with type arg = exp -> unit and type result = unit

    (** Test for equality. *)
    module EqualTo : FGN_OPN with type arg = exp and type result = bool

    (** Unify with another term. *)
    module UnifyWith :
      FGN_OPN with type arg = dec ctx * exp and type result = fgnUnify

    (** Fold a function over the subterms. *)
    val fold : csid * fgnExp -> (exp * 'a -> 'a) -> 'a -> 'a
  end

  (** Standard operations on foreign constraints. *)
  module FgnCnstrStd : sig
    (** Convert to internal syntax. *)
    module ToInternal :
      FGN_OPN with type arg = unit and type result = (dec ctx * exp) list

    (** Wake up a delayed foreign constraint. *)
    module Awake : FGN_OPN with type arg = unit and type result = bool

    (** Simplify a foreign constraint. *)
    module Simplify : FGN_OPN with type arg = unit and type result = bool
  end

  val arrow_ : exp * exp -> exp
  val conDecName : conDec -> string
  val conDecParent : conDec -> mid option
  val conDecImp : conDec -> int
  val conDecStatus : conDec -> status
  val conDecType : conDec -> exp
  val conDecBlock : conDec -> dctx * dec list
  val conDecUni : conDec -> uni
  val strDecName : strDec -> string
  val strDecParent : strDec -> mid option
  val sgnReset : unit -> unit
  val sgnSize : unit -> cid * mid
  val sgnAdd : conDec -> cid
  val sgnLookup : cid -> conDec
  val sgnApp : (cid -> unit) -> unit
  val sgnStructAdd : strDec -> mid
  val sgnStructLookup : mid -> strDec
  val constType : cid -> exp

  (** Type of [c] or [d]. *)
  val constDef : cid -> exp

  (** Definition of [d]. *)
  val constImp : cid -> int
  val constStatus : cid -> status
  val constUni : cid -> uni
  val constBlock : cid -> dctx * dec list

  (** Declaration contexts. *)
  val ctxDec : dctx * int -> dec

  (** Get a variable declaration. *)
  val blockDec : dctx * block * int -> dec

  (** Explicit substitutions. *)
  val id : sub

  (** Identity substitution. *)
  val shift : sub

  (** Shift substitution ([^]). *)
  val invShift : sub

  (** Inverse shift substitution ([^-1]). *)
  val bvarSub : int * sub -> front

  (** Bound-variable substitution application ([k[s]]). *)
  val frontSub : front * sub -> front

  (** Front substitution application ([H[s]]). *)
  val decSub : dec * sub -> dec

  (** Declaration substitution application ([x:V[s]]). *)
  val blockSub : block * sub -> block

  (** Block substitution application ([B[s]]). *)
  val comp : sub * sub -> sub

  (** Substitution composition ([s o s']). *)
  val dot1 : sub -> sub

  (** Dot-1 operation ([1 . (s o ^)]). *)
  val invDot1 : sub -> sub

  (** Inverse dot-1 operation ([(^ o s) o ^-1]). *)
  (** EVar-related functions. *)
  val newEVar : dctx * exp -> exp

  (** Create [X:G|-V, []]. *)
  val newAVar : unit -> exp

  (** Create a bare [A]. *)
  val newTypeVar : dctx -> exp

  (** Create [X:G|-type, []]. *)
  val newLVar : sub * (cid * sub) -> block

  (** Create [B:(l[^k],t)]. *)
  (** Definition-related functions. *)
  val headOpt : exp -> head option
  val ancestor : exp -> ancestor
  val defAncestor : cid -> ancestor

  (** Type-related functions. *)
  (** Do not expand type definitions. *)
  val targetHeadOpt : exp -> head option

  (** Target type family, or [None]. *)
  val targetHead : exp -> head

  (** Target type family. *)
  (** Expand type definitions. *)
  val targetFamOpt : exp -> cid option

  (** Target type family, or [None]. *)
  val targetFam : exp -> cid

  (** Target type family. *)
  (** Used in [Flit]. *)
  val rename : cid * string -> unit
end
(** Signature {!INTSYN}. *)
