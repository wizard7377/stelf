(* # 1 "src/lambda/intsyn.sig.ml" *)
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

(* # 1 "src/lambda/intsyn.fun.ml" *)
open! Basis

(* Internal Syntax *)
open Fgnopntable

(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
module MakeIntSyn (IntSyn__0 : sig
  module Global : GLOBAL
end) : INTSYN = struct
  type nonrec cid = int

  (* Constant identifier        *)
  type nonrec name = string

  (* Variable name              *)
  type nonrec mid = int

  (* Structure identifier       *)
  type nonrec csid = int

  (* CS module identifier       *)
  (* Contexts *)
  type 'a ctx_ = Null | Decl of 'a ctx_ * 'a

  let null_ = Null

  (* Contexts                   *)
  (* G ::= .                    *)
  (*     | G, D                 *)
  (* ctxPop (G) => G'
     Invariant: G = G',D
  *)
  let rec ctxPop (Decl (g_, d_)) = g_

  exception Error of string

  (* raised if out of space     *)
  (* ctxLookup (G, k) = D, kth declaration in G from right to left
     Invariant: 1 <= k <= |G|, where |G| is length of G
  *)
  let rec ctxLookup = function
    | Decl (g'_, d_), 1 -> d_
    | Decl (g'_, _), k' -> ctxLookup (g'_, k' - 1)

  (*    | ctxLookup (Null, k') = (print (""Looking up k' = "" ^ Int.toString k' ^ ""\n""); raise Error ""Out of Bounce\n"")*)
  (* ctxLookup (Null, k')  should not occur by invariant *)
  (* ctxLength G = |G|, the number of declarations in G *)
  let rec ctxLength g_ =
    let rec ctxLength' = function
      | Null, n -> n
      | Decl (g_, _), n -> ctxLength' (g_, n + 1)
    in
    ctxLength' (g_, 0)

  type nonrec fgnExp_ = exn

  (* foreign expression representation *)
  exception UnexpectedFgnExp of fgnExp_

  (* raised by a constraint solver
                                           if passed an incorrect arg *)
  type nonrec fgnCnstr_ = exn

  (* foreign unification constraint
                                           representation *)
  exception UnexpectedFgnCnstr of fgnCnstr_

  (* raised by a constraint solver
                                           if passed an incorrect arg *)
  type depend_ = No | Maybe | Meta

  (* Dependency information     *)
  (* P ::= No                   *)
  (*     | Maybe                *)
  (*     | Meta                 *)
  (* Expressions *)
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
    | FVar of name * exp_ * sub_
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
    | Dec of name option * exp_
    | BDec of name option * (cid * sub_)
    | ADec of name option * int
    | NDec of name option

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
  (*     | bPi (D, P). V         *)
  (*     | C @ S                *)
  (*     | U @ S                *)
  (*     | lam D. U             *)
  (*     | X<I> : G|-V, Cnstr   *)
  (*     | U[s]                 *)
  (*     | A<I>                 *)
  (*     | n (linear, fully applied) *)
  (* grafting variable *)
  (*     | (foreign expression) *)
  (* Heads:                     *)
  (* H ::= k                    *)
  (*     | c                    *)
  (*     | #k(b)                *)
  (*     | c#                   *)
  (*     | d                    *)
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
  (*     | U (assignable)       *)
  (*     | _x                   *)
  (*     | _                    *)
  (* Declarations:              *)
  (* D ::= x:V                  *)
  (*     | v:l[s]               *)
  (*     | v[^-d]               *)
  (* Blocks:                    *)
  (* b ::= v                    *)
  (*     | L(l[^k],t)           *)
  (*     | u1, ..., Un          *)
  (* Constraints *)
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
  (* Residual of foreign unify  *)
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

  (*  exception Error of string              raised if out of space      *)
  module FgnExpStd = struct
    module ToInternal = FgnOpnTable (struct
      type nonrec arg = unit
      type nonrec result = exp_
    end)

    module Map = FgnOpnTable (struct
      type nonrec arg = exp_ -> exp_
      type nonrec result = exp_
    end)

    module App = FgnOpnTable (struct
      type nonrec arg = exp_ -> unit
      type nonrec result = unit
    end)

    module EqualTo = FgnOpnTable (struct
      type nonrec arg = exp_
      type nonrec result = bool
    end)

    module UnifyWith = FgnOpnTable (struct
      type nonrec arg = dec_ ctx_ * exp_
      type nonrec result = fgnUnify_
    end)

    let rec fold csfe f b =
      let r = ref b in
      let rec g u_ = r := f (u_, !r) in
      begin
        App.apply csfe g;
        !r
      end
  end

  module FgnCnstrStd = struct
    module ToInternal = FgnOpnTable (struct
      type nonrec arg = unit
      type nonrec result = (dec_ ctx_ * exp_) list
    end)

    module Awake = FgnOpnTable (struct
      type nonrec arg = unit
      type nonrec result = bool
    end)

    module Simplify = FgnOpnTable (struct
      type nonrec arg = unit
      type nonrec result = bool
    end)
  end

  let arrow_ (a, b) = Pi ((Dec (None, a), No), b)

  let rec conDecName = function
    | ConDec (name, _, _, _, _, _) -> name
    | ConDef (name, _, _, _, _, _, _) -> name
    | AbbrevDef (name, _, _, _, _, _) -> name
    | SkoDec (name, _, _, _, _) -> name
    | BlockDec (name, _, _, _) -> name
    | BlockDef (name, _, _) -> name

  let rec conDecParent = function
    | ConDec (_, parent, _, _, _, _) -> parent
    | ConDef (_, parent, _, _, _, _, _) -> parent
    | AbbrevDef (_, parent, _, _, _, _) -> parent
    | SkoDec (_, parent, _, _, _) -> parent
    | BlockDec (_, parent, _, _) -> parent
    | BlockDef (_, parent, _) -> parent

  (* conDecImp (CD) = k

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then k stands for the number of implicit elements.
  *)
  let rec conDecImp = function
    | ConDec (_, _, i, _, _, _) -> i
    | ConDef (_, _, i, _, _, _, _) -> i
    | AbbrevDef (_, _, i, _, _, _) -> i
    | SkoDec (_, _, i, _, _) -> i
    | BlockDec (_, _, _, _) -> 0

  (* watch out -- carsten *)
  let rec conDecStatus = function
    | ConDec (_, _, _, status, _, _) -> status
    | _ -> Normal

  (* conDecType (CD) =  V

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then V is the respective type
  *)
  let rec conDecType = function
    | ConDec (_, _, _, _, v_, _) -> v_
    | ConDef (_, _, _, _, v_, _, _) -> v_
    | AbbrevDef (_, _, _, _, v_, _) -> v_
    | SkoDec (_, _, _, v_, _) -> v_

  (* conDecBlock (CD) =  (Gsome, Lpi)

     Invariant:
     If   CD is block definition
     then Gsome is the context of some variables
     and  Lpi is the list of pi variables
  *)
  let rec conDecBlock (BlockDec (_, _, gsome_, lpi_)) = (gsome_, lpi_)

  (* conDecUni (CD) =  L

     Invariant:
     If   CD is either a declaration, definition, abbreviation, or
          a Skolem constant
     then L is the respective universe
  *)
  let rec conDecUni = function
    | ConDec (_, _, _, _, _, l_) -> l_
    | ConDef (_, _, _, _, _, l_, _) -> l_
    | AbbrevDef (_, _, _, _, _, l_) -> l_
    | SkoDec (_, _, _, _, l_) -> l_

  let rec strDecName (StrDec (name, _)) = name
  let rec strDecParent (StrDec (_, parent)) = parent

  open! struct
    let maxCid = Global.maxCid
    let dummyEntry = ConDec ("", None, 0, Normal, Uni Kind, Kind)
    let sgnArray = (Array.array (maxCid + 1, dummyEntry) : conDec_ Array.array)
    let nextCid = ref 0
    let maxMid = Global.maxMid

    let sgnStructArray =
      (Array.array (maxMid + 1, StrDec ("", None)) : strDec_ Array.array)

    let nextMid = ref 0
  end

  (* Invariants *)
  (* Constant declarations are all well-typed *)
  (* Constant declarations are stored in beta-normal form *)
  (* All definitions are strict in all their arguments *)
  (* If Const(cid) is valid, then sgnArray(cid) = ConDec _ *)
  (* If Def(cid) is valid, then sgnArray(cid) = ConDef _ *)
  let rec sgnClean i =
    begin if i >= !nextCid then ()
    else begin
      Array.update (sgnArray, i, dummyEntry);
      sgnClean (i + 1)
    end
    end

  let rec sgnReset () =
    begin
      sgnClean 0;
      begin
        nextCid := 0;
        nextMid := 0
      end
    end
  (* Fri Dec 20 12:04:24 2002 -fp *)
  (* this circumvents a space leak *)

  let rec sgnSize () = (!nextCid, !nextMid)

  let rec sgnAdd conDec =
    let cid = !nextCid in
    begin if cid > maxCid then
      raise
        (Error
           (("Global signature size " ^ Int.toString (maxCid + 1)) ^ " exceeded"))
    else begin
      Array.update (sgnArray, cid, conDec);
      begin
        nextCid := cid + 1;
        cid
      end
    end
    end

  (* 0 <= cid < !nextCid *)
  let rec sgnLookup cid = Array.sub (sgnArray, cid)

  let rec sgnApp f =
    let rec sgnApp' cid =
      begin if cid = !nextCid then ()
      else begin
        f cid;
        sgnApp' (cid + 1)
      end
      end
    in
    sgnApp' 0

  let rec sgnStructAdd strDec =
    let mid = !nextMid in
    begin if mid > maxMid then
      raise
        (Error
           (("Global signature size " ^ Int.toString (maxMid + 1)) ^ " exceeded"))
    else begin
      Array.update (sgnStructArray, mid, strDec);
      begin
        nextMid := mid + 1;
        mid
      end
    end
    end

  (* 0 <= mid < !nextMid *)
  let rec sgnStructLookup mid = Array.sub (sgnStructArray, mid)

  (* A hack used in Flit - jcreed 6/05 *)
  let rec rename (cid, new_) =
    let newConDec =
      begin match sgnLookup cid with
      | ConDec (n, m, i, s, e, u) -> ConDec (new_, m, i, s, e, u)
      | ConDef (n, m, i, e, e', u, a) -> ConDef (new_, m, i, e, e', u, a)
      | AbbrevDef (n, m, i, e, e', u) -> AbbrevDef (new_, m, i, e, e', u)
      | BlockDec (n, m, d, d') -> BlockDec (new_, m, d, d')
      | SkoDec (n, m, i, e, u) -> SkoDec (new_, m, i, e, u)
      end
    in
    Array.update (sgnArray, cid, newConDec)

  let rec constDef d =
    begin match sgnLookup d with
    | ConDef (_, _, _, u_, _, _, _) -> u_
    | AbbrevDef (_, _, _, u_, _, _) -> u_
    end

  let rec constType c = conDecType (sgnLookup c)
  let rec constImp c = conDecImp (sgnLookup c)
  let rec constUni c = conDecUni (sgnLookup c)
  let rec constBlock c = conDecBlock (sgnLookup c)

  let rec constStatus c =
    begin match sgnLookup c with
    | ConDec (_, _, _, status, _, _) -> status
    | _ -> Normal
    end

  (* Explicit Substitutions *)
  (* id = ^0

     Invariant:
     G |- id : G        id is patsub
  *)
  let id = Shift 0

  (* shift = ^1

     Invariant:
     G, V |- ^ : G       ^ is patsub
  *)
  let shift = Shift 1

  (* invShift = ^-1 = _.^0
     Invariant:
     G |- ^-1 : G, V     ^-1 is patsub
  *)
  let invShift = Dot (Undef, id)

  (* comp (s1, s2) = s'

     Invariant:
     If   G'  |- s1 : G
     and  G'' |- s2 : G'
     then s'  = s1 o s2
     and  G'' |- s1 o s2 : G

     If  s1, s2 patsub
     then s' patsub
   *)
  let rec comp = function
    | Shift 0, s -> s
    | s, Shift 0 -> s
    | Shift n, Dot (ft_, s) -> comp (Shift (n - 1), s)
    | Shift n, Shift m -> Shift (n + m)
    | Dot (ft_, s), s' -> Dot (frontSub (ft_, s'), comp (s, s'))
  (* Sat Feb 14 10:15:16 1998 -fp *)
  (* roughly 15% on standard suite for Twelf 1.1 *)
  (* next line is an optimization *)

  and bvarSub = function
    | 1, Dot (ft_, s) -> ft_
    | n, Dot (ft_, s) -> bvarSub (n - 1, s)
    | n, Shift k -> Idx (n + k)

  and blockSub = function
    | Bidx k, s -> begin
        match bvarSub (k, s) with Idx k' -> Bidx k' | Block b_ -> b_
      end
    | LVar ({ contents = Some b_ }, sk, _), s -> blockSub (b_, comp (sk, s))
    | LVar (({ contents = None } as r), sk, (l, t)), s ->
        LVar (r, comp (sk, s), (l, t))
    | (Inst uLs_ as l_), s' -> Inst (map (function u_ -> EClo (u_, s')) uLs_)

  (* comp(^k, s) = ^k' for some k' by invariant *)
  (* was:
        LVar (r, comp(sk, s), (l, comp (t, s)))
        July 22, 2010 -fp -cs
       *)

  (* Thu Dec  6 20:30:26 2001 -fp !!! *)
  (* where is this needed? *)
  (* Since always . |- t : Gsome, discard s *)
  (* --cs Sun Dec  1 11:25:41 2002 *)
  (* -fp Sun Dec  1 21:18:30 2002 *)
  and frontSub = function
    | Idx n, s -> bvarSub (n, s)
    | Exp u_, s -> Exp (EClo (u_, s))
    | Undef, s -> Undef
    | Block b_, s -> Block (blockSub (b_, s))

  (* bvarSub (n, s) = Ft'

      Invariant:
     If    G |- s : G'    G' |- n : V
     then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
       or  Ft' = ^(n+k)     if  s = Ft1 .. Ftm ^k   and m<n
     and   G |- Ft' : V [s]
  *)
  (* blockSub (B, s) = B'

     Invariant:
     If   G |- s : G'
     and  G' |- B block
     then G |- B' block
     and  B [s] == B'
  *)
  (* in front of substitutions, first case is irrelevant *)
  (* Sun Dec  2 11:56:41 2001 -fp *)
  (* this should be right but somebody should verify *)
  (* frontSub (Ft, s) = Ft'

     Invariant:
     If   G |- s : G'     G' |- Ft : V
     then Ft' = Ft [s]
     and  G |- Ft' : V [s]

     NOTE: EClo (U, s) might be undefined, so if this is ever
     computed eagerly, we must introduce an ""Undefined"" exception,
     raise it in whnf and handle it here so Exp (EClo (U, s)) => Undef
  *)
  (* decSub (x:V, s) = D'

     Invariant:
     If   G  |- s : G'    G' |- V : L
     then D' = x:V[s]
     and  G  |- V[s] : L
  *)
  (* First line is an optimization suggested by cs *)
  (* D[id] = D *)
  (* Sat Feb 14 18:37:44 1998 -fp *)
  (* seems to have no statistically significant effect *)
  (* undo for now Sat Feb 14 20:22:29 1998 -fp *)
  (*
  fun decSub (D, Shift(0)) = D
    | decSub (Dec (x, V), s) = Dec (x, EClo (V, s))
  *)
  let rec decSub = function
    | Dec (x, v_), s -> Dec (x, EClo (v_, s))
    | NDec x, s -> NDec x
    | BDec (n, (l, t)), s -> BDec (n, (l, comp (t, s)))

  (* dot1 (s) = s'

     Invariant:
     If   G |- s : G'
     then s' = 1. (s o ^)
     and  for all V s.t.  G' |- V : L
          G, V[s] |- s' : G', V

     If s patsub then s' patsub
  *)
  (* first line is an optimization *)
  (* roughly 15% on standard suite for Twelf 1.1 *)
  (* Sat Feb 14 10:16:16 1998 -fp *)
  let rec dot1 = function Shift 0 as s -> s | s -> Dot (Idx 1, comp (s, shift))

  (* invDot1 (s) = s'
     invDot1 (1. s' o ^) = s'

     Invariant:
     s = 1 . s' o ^
     If G' |- s' : G
     (so G',V[s] |- s : G,V)
  *)
  let rec invDot1 s = comp (comp (shift, s), invShift)

  (* Declaration Contexts *)
  (* ctxDec (G, k) = x:V
     Invariant:
     If      |G| >= k, where |G| is size of G,
     then    G |- k : V  and  G |- V : L
  *)
  let rec ctxDec (g_, k) =
    let rec ctxDec' = function
      | Decl (g'_, Dec (x, v'_)), 1 -> Dec (x, EClo (v'_, Shift k))
      | Decl (g'_, BDec (n, (l, s))), 1 -> BDec (n, (l, comp (s, Shift k)))
      | Decl (g'_, _), k' -> ctxDec' (g'_, k' - 1)
    in
    ctxDec' (g_, k)

  (* ctxDec' (G'', k') = x:V
             where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
  (* ctxDec' (Null, k')  should not occur by invariant *)

  (* blockDec (G, v, i) = V

     Invariant:
     If   G (v) = l[s]
     and  Sigma (l) = SOME Gsome BLOCK Lblock
     and  G |- s : Gsome
     then G |- pi (v, i) : V
  *)
  let rec blockDec (g_, (Bidx k as v), i) =
    let (BDec (_, (l, s))) = ctxDec (g_, k) in
    let gsome_, lblock_ = conDecBlock (sgnLookup l) in
    let rec blockDec' = function
      | t, d_ :: l_, 1, j -> decSub (d_, t)
      | t, _ :: l_, n, j ->
          blockDec' (Dot (Exp (Root (Proj (v, j), Nil)), t), l_, n - 1, j + 1)
    in
    blockDec' (s, lblock_, i, 1)
  (* G |- s : Gsome *)

  (* EVar related functions *)
  (* newEVar (G, V) = newEVarCnstr (G, V, nil) *)
  let rec newEVar (g_, v_) = EVar (ref None, g_, v_, ref [])

  (* newAVar G = new AVar (assignable variable) *)
  (* AVars carry no type, ctx, or cnstr *)
  let rec newAVar () = AVar (ref None)

  (* newTypeVar (G) = X, X new
     where G |- X : type
  *)
  let rec newTypeVar g_ = EVar (ref None, g_, Uni Type, ref [])

  (* newLVar (l, s) = (l[s]) *)
  let rec newLVar (sk, (cid, t)) = LVar (ref None, sk, (cid, t))

  (* Definition related functions *)
  (* headOpt (U) = SOME(H) or NONE, U should be strict, normal *)
  let rec headOpt = function
    | Root (h_, _) -> Some h_
    | Lam (_, u_) -> headOpt u_
    | _ -> None

  let rec ancestor' = function
    | None -> Anc (None, 0, None)
    | Some (Const c) -> Anc (Some c, 1, Some c)
    | Some (Def d) -> begin
        match sgnLookup d with
        | ConDef (_, _, _, _, _, _, Anc (_, height, cOpt)) ->
            Anc (Some d, height + 1, cOpt)
      end
    | Some _ -> Anc (None, 0, None)
  (* FgnConst possible, BVar impossible by strictness *)

  (* ancestor(U) = ancestor info for d = U *)
  let rec ancestor u_ = ancestor' (headOpt u_)

  (* defAncestor(d) = ancestor of d, d must be defined *)
  let rec defAncestor d =
    begin match sgnLookup d with ConDef (_, _, _, _, _, _, anc) -> anc
    end

  (* Type related functions *)
  (* targetHeadOpt (V) = SOME(H) or NONE
     where H is the head of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does not expand type definitions.
  *)
  (* should there possibly be a FgnConst case? also targetFamOpt -kw *)
  let rec targetHeadOpt = function
    | Root (h_, _) -> Some h_
    | Pi (_, v_) -> targetHeadOpt v_
    | Redex (v_, s_) -> targetHeadOpt v_
    | Lam (_, v_) -> targetHeadOpt v_
    | EVar ({ contents = Some v_ }, _, _, _) -> targetHeadOpt v_
    | EClo (v_, s) -> targetHeadOpt v_
    | _ -> None

  (* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)
  (* Root(Skonst _, _) can't occur *)
  (* targetHead (A) = a
     as in targetHeadOpt, except V must be a valid type
  *)
  let rec targetHead a_ = valOf (targetHeadOpt a_)

  (* targetFamOpt (V) = SOME(cid) or NONE
     where cid is the type family of the atomic target type of V,
     NONE if V is a kind or object or have variable type.
     Does expand type definitions.
  *)
  let rec targetFamOpt = function
    | Root (Const cid, _) -> Some cid
    | Pi (_, v_) -> targetFamOpt v_
    | Root (Def cid, _) -> targetFamOpt (constDef cid)
    | Redex (v_, s_) -> targetFamOpt v_
    | Lam (_, v_) -> targetFamOpt v_
    | EVar ({ contents = Some v_ }, _, _, _) -> targetFamOpt v_
    | EClo (v_, s) -> targetFamOpt v_
    | _ -> None

  (* Root(Bvar _, _), Root(FVar _, _), Root(FgnConst _, _),
         EVar(ref NONE,..), Uni, FgnExp _
      *)
  (* Root(Skonst _, _) can't occur *)
  (* targetFam (A) = a
     as in targetFamOpt, except V must be a valid type
  *)
  let rec targetFam a_ = valOf (targetFamOpt a_)
end

(* functor IntSyn *)
module IntSyn = MakeIntSyn (struct
  module Global = Global
end)

(* # 1 "src/lambda/intsyn.sml.ml" *)
