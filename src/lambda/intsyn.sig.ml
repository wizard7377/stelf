open! Basis
open Fgnopn

(* Internal Syntax *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
module type INTSYN = sig
  type nonrec cid = int

  (* Constant identifier        *)
  type nonrec mid = int

  (* Structure identifier       *)
  type nonrec csid = int

  (* CS module identifier       *)
  type nonrec fgnExp_ = exn

  (* foreign expression representation *)
  exception UnexpectedFgnExp of fgnExp_

  (* raised by a constraint solver
					   if passed an incorrect arg *)
  type nonrec fgnCnstr_ = exn

  (* foreign constraint representation *)
  exception UnexpectedFgnCnstr of fgnCnstr_

  (* raised by a constraint solver
                                           if passed an incorrect arg *)
  (* Contexts *)
  type 'a ctx_ = Null | Decl of 'a ctx_ * 'a

  val null_ : 'a ctx_

  (* Contexts                   *)
  (* G ::= .                    *)
  (*     | G, D                 *)
  val ctxPop : 'a ctx_ -> 'a ctx_
  val ctxLookup : 'a ctx_ * int -> 'a
  val ctxLength : 'a ctx_ -> int

  type depend_ = No | Maybe | Meta

  (* Dependency information     *)
  (* P ::= No                   *)
  (*     | Maybe                *)
  (*     | Meta                 *)
  (* expressions *)
  type uni_ = Kind | Type

  (* Universes:                 *)
  (* L ::= Kind                 *)
  (*     | Type                 *)
  type exp_ =
    | Uni of uni_
    | Pi of (dec_ * depend_) * exp_
    | Root of head_ * spine_
    | Redex of exp_ * spine_
    | Lam of dec_ * exp_
    | EVar of exp_ option ref * dec_ ctx_ * exp_ * cnstr_ ref list ref
    | EClo of exp_ * sub_
    | AVar of exp_ option ref
    | FgnExp of csid * fgnExp_
    | NVar of int

  and head_ =
    | BVar of int
    | Const of cid
    | Proj of block_ * int
    | Skonst of cid
    | Def of cid
    | NSDef of cid
    | FVar of string * exp_ * sub_
    | FgnConst of csid * conDec_

  and spine_ = Nil | App of exp_ * spine_ | SClo of spine_ * sub_
  and sub_ = Shift of int | Dot of front_ * sub_

  and front_ =
    | Idx of int
    | Exp of exp_
    | Axp of exp_
    | Block of block_
    | Undef

  and dec_ =
    | Dec of string option * exp_
    | BDec of string option * (cid * sub_)
    | ADec of string option * int
    | NDec of string option

  and block_ =
    | Bidx of int
    | LVar of block_ option ref * sub_ * (cid * sub_)
    | Inst of exp_ list

  and cnstr_ =
    | Solved
    | Eqn of dec_ ctx_ * exp_ * exp_
    | FgnCnstr of csid * fgnCnstr_

  and status_ =
    | Normal
    | Constraint of csid * (dec_ ctx_ * spine_ * int -> exp_ option)
    | Foreign of csid * (spine_ -> exp_)

  and fgnUnify_ = Succeed of fgnUnifyResidual_ list | Fail

  and fgnUnifyResidual_ =
    | Assign of dec_ ctx_ * exp_ * exp_ * sub_
    | Delay of exp_ * cnstr_ ref

  and conDec_ =
    | ConDec of
        string
        * mid option
        * int
        * status_
        * exp_
        * uni_ (* a : K : kind  or           *)
    | ConDef of string * mid option * int * exp_ * exp_ * uni_ * ancestor_
    (* d = M : A : type           *)
    (* a = A : K : kind  or       *)
    | AbbrevDef of
        string
        * mid option
        * int
        * exp_
        * exp_
        * uni_ (* a = A : K : kind  or       *)
    | BlockDec of
        string
        * mid option
        * dec_ ctx_
        * dec_ list (* %block l : SOME G1 PI G2   *)
    | BlockDef of string * mid option * cid list
    | SkoDec of
        string * mid option * int * exp_ * uni_ (* sa: K : kind  or           *)

  and ancestor_ = Anc of cid option * int * cid option

  (* Expressions:               *)
  (* U ::= L                    *)
  (*     | Pi (D, P). V         *)
  (*     | H @ S                *)
  (*     | U @ S                *)
  (*     | lam D. U             *)
  (*     | X<I> : G|-V, Cnstr   *)
  (*     | U[s]                 *)
  (*     | A<I>                 *)
  (*     | (foreign expression) *)
  (*     | n (linear, 
                                               fully applied variable
                                               used in indexing       *)
  (* Head:                      *)
  (* H ::= k                    *)
  (*     | c                    *)
  (*     | #k(b)                *)
  (*     | c#                   *)
  (*     | d (strict)           *)
  (*     | d (non strict)       *)
  (*     | F[s]                 *)
  (*     | (foreign constant)   *)
  (* Spines:                    *)
  (* S ::= Nil                  *)
  (*     | U ; S                *)
  (*     | S[s]                 *)
  (* Explicit substitutions:    *)
  (* s ::= ^n                   *)
  (*     | Ft.s                 *)
  (* Fronts:                    *)
  (* Ft ::= k                   *)
  (*     | U                    *)
  (*     | U                    *)
  (*     | _x                   *)
  (*     | _                    *)
  (* Declarations:              *)
  (* D ::= x:V                  *)
  (*     | v:l[s]               *)
  (*     | v[^-d]               *)
  (* Blocks:                    *)
  (* b ::= v                    *)
  (*     | L(l[^k],t)           *)
  (*     | U1, ..., Un          *)
  (* It would be better to consider having projections count
     like substitutions, then we could have Inst of Sub here, 
     which would simplify a lot of things.  

     I suggest however to wait until the next big overhaul 
     of the system -- cs *)
  (*  | BClo of Block * Sub                      | b[s]                  *)
  (* constraints *)
  (* Constraint:                *)
  (* Cnstr ::= solved           *)
  (*         | G|-(U1 == U2)    *)
  (*         | (foreign)        *)
  (* Status of a constant:      *)
  (*   inert                    *)
  (*   acts as constraint       *)
  (*   is converted to foreign  *)
  (* Result of foreign unify    *)
  (* succeed with a list of residual operations *)
  (* perform the assignment G |- X = U [ss] *)
  (* delay cnstr, associating it with all the rigid EVars in U  *)
  (* Global signature *)
  (* Constant declaration       *)
  (* c : A : type               *)
  (* Ancestor info for d or a   *)
  (* d = M : A : type           *)
  (* %block l = (l1 | ... | ln) *)
  (* sc: A : type               *)
  (* Ancestor of d or a         *)
  (* head(expand(d)), height, head(expand[height](d)) *)
  (* NONE means expands to {x:A}B *)
  type strDec_ = StrDec of string * mid option

  (* Structure declaration      *)
  (* Form of constant declaration *)
  type conDecForm_ = FromCS | Ordinary | Clause

  (* from constraint domain *)
  (* ordinary declaration *)
  (* %clause declaration *)
  (* Type abbreviations *)
  type nonrec dctx = dec_ ctx_

  (* G = . | G,D                *)
  type nonrec eclo = exp_ * sub_

  (* Us = U[s]                  *)
  type nonrec bclo = block_ * sub_

  (* Bs = B[s]                  *)
  type nonrec cnstr = cnstr_ ref

  exception Error of string

  (* raised if out of space     *)
  (* standard operations on foreign expressions *)
  module FgnExpStd : sig
    (* convert to internal syntax *)
    module ToInternal : FGN_OPN with type arg = unit and type result = exp_

    (* apply function to subterms *)
    module Map : FGN_OPN with type arg = exp_ -> exp_ and type result = exp_

    (* apply function to subterms, for effect *)
    module App : FGN_OPN with type arg = exp_ -> unit and type result = unit

    (* test for equality *)
    module EqualTo : FGN_OPN with type arg = exp_ and type result = bool

    (* unify with another term *)
    module UnifyWith :
      FGN_OPN with type arg = dec_ ctx_ * exp_ and type result = fgnUnify_

    (* fold a function over the subterms *)
    val fold : csid * fgnExp_ -> (exp_ * 'a -> 'a) -> 'a -> 'a
  end

  (* standard operations on foreign constraints *)
  module FgnCnstrStd : sig
    (* convert to internal syntax *)
    module ToInternal :
      FGN_OPN with type arg = unit and type result = (dec_ ctx_ * exp_) list

    (* awake *)
    module Awake : FGN_OPN with type arg = unit and type result = bool

    (* simplify *)
    module Simplify : FGN_OPN with type arg = unit and type result = bool
  end

  val arrow_ : exp_ * exp_ -> exp_
  val conDecName : conDec_ -> string
  val conDecParent : conDec_ -> mid option
  val conDecImp : conDec_ -> int
  val conDecStatus : conDec_ -> status_
  val conDecType : conDec_ -> exp_
  val conDecBlock : conDec_ -> dctx * dec_ list
  val conDecUni : conDec_ -> uni_
  val strDecName : strDec_ -> string
  val strDecParent : strDec_ -> mid option
  val sgnReset : unit -> unit
  val sgnSize : unit -> cid * mid
  val sgnAdd : conDec_ -> cid
  val sgnLookup : cid -> conDec_
  val sgnApp : (cid -> unit) -> unit
  val sgnStructAdd : strDec_ -> mid
  val sgnStructLookup : mid -> strDec_
  val constType : cid -> exp_

  (* type of c or d             *)
  val constDef : cid -> exp_

  (* definition of d            *)
  val constImp : cid -> int
  val constStatus : cid -> status_
  val constUni : cid -> uni_
  val constBlock : cid -> dctx * dec_ list

  (* Declaration Contexts *)
  val ctxDec : dctx * int -> dec_

  (* get variable declaration   *)
  val blockDec : dctx * block_ * int -> dec_

  (* Explicit substitutions *)
  val id : sub_

  (* id                         *)
  val shift : sub_

  (* ^                          *)
  val invShift : sub_

  (* ^-1                        *)
  val bvarSub : int * sub_ -> front_

  (* k[s]                       *)
  val frontSub : front_ * sub_ -> front_

  (* H[s]                       *)
  val decSub : dec_ * sub_ -> dec_

  (* x:V[s]                     *)
  val blockSub : block_ * sub_ -> block_

  (* B[s]                       *)
  val comp : sub_ * sub_ -> sub_

  (* s o s'                     *)
  val dot1 : sub_ -> sub_

  (* 1 . (s o ^)                *)
  val invDot1 : sub_ -> sub_

  (* (^ o s) o ^-1)             *)
  (* EVar related functions *)
  val newEVar : dctx * exp_ -> exp_

  (* creates X:G|-V, []         *)
  val newAVar : unit -> exp_

  (* creates A (bare)           *)
  val newTypeVar : dctx -> exp_

  (* creates X:G|-type, []      *)
  val newLVar : sub_ * (cid * sub_) -> block_

  (* creates B:(l[^k],t)        *)
  (* Definition related functions *)
  val headOpt : exp_ -> head_ option
  val ancestor : exp_ -> ancestor_
  val defAncestor : cid -> ancestor_

  (* Type related functions *)
  (* Not expanding type definitions *)
  val targetHeadOpt : exp_ -> head_ option

  (* target type family or NONE *)
  val targetHead : exp_ -> head_

  (* target type family         *)
  (* Expanding type definitions *)
  val targetFamOpt : exp_ -> cid option

  (* target type family or NONE *)
  val targetFam : exp_ -> cid

  (* target type family         *)
  (* Used in Flit *)
  val rename : cid * string -> unit
end
(* signature INTSYN *)
