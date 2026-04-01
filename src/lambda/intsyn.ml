open! Basis
open Fgnopntable
include Intsyn_intf

module type INTSYN = Intsyn_intf.INTSYN


(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
module MakeIntSyn (IntSyn__0 : sig
  module Global : GLOBAL
end) : INTSYN = struct
  type cid = int [@@deriving eq, ord, show]
  (** Constant identifier *)

  type nonrec name = string
  (** Variable name *)

  let equal_name (a : name) b = a = b
  let compare_name (a : name) b = compare a b
  let pp_name = Format.pp_print_string
  let show_name s = s

  type mid = int [@@deriving eq, ord, show]
  (** Structure identifier *)

  type csid = int [@@deriving eq, ord, show]
  (** CS module identifier *)

  (** Contexts *)
  type 'a ctx = Null | Decl of 'a ctx * 'a [@@deriving eq, ord, show]

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

  type fgnExp = exn
  (** foreign expression representation *)

  let equal_fgnExp _ _ = false
  let compare_fgnExp _ _ = 0
  let pp_fgnExp fmt e = Format.pp_print_string fmt (Printexc.to_string e)
  let show_fgnExp e = Printexc.to_string e

  (* foreign expression representation *)
  exception UnexpectedFgnExp of fgnExp

  (* raised by a constraint solver
      if passed an incorrect arg *)
  (* foreign unification constraint
      representation *)
  type fgnCnstr = exn

  let equal_fgnCnstr _ _ = false
  let compare_fgnCnstr _ _ = 0
  let pp_fgnCnstr fmt e = Format.pp_print_string fmt (Printexc.to_string e)
  let show_fgnCnstr e = Printexc.to_string e

  exception UnexpectedFgnCnstr of fgnCnstr

  (* raised by a constraint solver
     if passed an incorrect arg *)
  (* Dependency information
     P ::= No
         | Maybe
         | Meta *)
  type depend = No | Maybe | Meta
  [@@deriving eq, ord, show { with_path = false }]

  (* Expressions
     Universes:
     L ::= Kind
         | Type *)
  type uni = Kind | Type [@@deriving eq, ord, show]

  (* Expressions:
     U ::= L
         | bPi (D, P). V
         | C @ S
         | U @ S
         | lam D. U
         | X<I> : G|-V, Cnstr
         | U[s]
         | A<I>
         | n (linear, fully applied)
         | (foreign expression)
     Heads:
     H ::= k | c | #k(b) | c# | d | d (non strict) | F[s] | (foreign constant)
     Spines:
     S ::= Nil | U ; S | S[s]
     Explicit substitutions:
     s ::= ^n | Ft.s
     Fronts:
     Ft ::= k | U | U (assignable) | _x | _
     Declarations:
     D ::= x:V | v:l[s] | v[^-d]
     Blocks:
     b ::= v | L(l[^k],t) | u1, ..., Un
     Constraints:
     Cnstr ::= solved | G|-(U1 == U2) | (foreign)
     Status of a constant:
       inert | acts as constraint | is converted to foreign
     Result/residual of foreign unify:
       succeed with a list of residual operations
       perform the assignment G |- X = U [ss]
       delay cnstr, associating it with all rigid EVars in U
     Global signature notes:
       c : A : type
       d = M : A : type
       %block l = (l1 | ... | ln)
       sc: A : type
       ancestor: head(expand(d)), height, head(expand[height](d))
       NONE means expands to {x:A}B *)
  type exp =
    | Uni of uni
    | Pi of (dec * depend) * exp
    | Root of head * spine
    | Redex of exp * spine
    | Lam of dec * exp
    | EVar of exp option ref * dec ctx * exp * cnstr_ ref list ref
    | EClo of exp * sub
    | AVar of exp option ref
    | FgnExp of csid * fgnExp
    | NVar of int
  [@@deriving eq, ord, show { with_path = false }]

  and head =
    | BVar of int
    | Const of cid
    | Proj of block * int
    | Skonst of cid
    | Def of cid
    | NSDef of cid
    | FVar of name * exp * sub
    | FgnConst of csid * conDec
  [@@deriving eq, ord, show { with_path = false }]

  and spine = Nil | App of exp * spine | SClo of spine * sub
  [@@deriving eq, ord, show { with_path = false }]

  and sub = Shift of int | Dot of front * sub
  [@@deriving eq, ord, show { with_path = false }]

  and front = Idx of int | Exp of exp | Axp of exp | Block of block | Undef

  and dec =
    | Dec of name option * exp
    | BDec of name option * (cid * sub)
    | ADec of name option * int
    | NDec of name option
  [@@deriving eq, ord, show { with_path = false }]

  and block =
    | Bidx of int
    | LVar of block option ref * sub * (cid * sub)
    | Inst of exp list

  and cnstr_ =
    | Solved
    | Eqn of dec ctx * exp * exp
    | FgnCnstr of csid * fgnCnstr
  [@@deriving eq, ord, show { with_path = false }]

  and status =
    | Normal
    | Constraint of
        csid
        * ((dec ctx * spine * int -> exp option)
          [@equal fun _ _ -> false]
          [@compare fun _ _ -> 0]
          [@printer fun fmt _ -> Format.pp_print_string fmt "<fun>"])
    | Foreign of
        csid
        * ((spine -> exp)
          [@equal fun _ _ -> false]
          [@compare fun _ _ -> 0]
          [@printer fun fmt _ -> Format.pp_print_string fmt "<fun>"])
  [@@deriving eq, ord, show { with_path = false }]

  and fgnUnify = Succeed of fgnUnifyResidual list | Fail

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
        * uni (* a : K : kind  or           *)
    | ConDef of string * mid option * int * exp * exp * uni * ancestor
    (* d = M : A : type           *)
    (* a = A : K : kind  or       *)
    | AbbrevDef of
        string
        * mid option
        * int
        * exp
        * exp
        * uni (* a = A : K : kind  or       *)
    | BlockDec of
        string
        * mid option
        * dec ctx
        * dec list (* %block l : SOME G1 PI G2   *)
    | BlockDef of string * mid option * cid list
    | SkoDec of
        string * mid option * int * exp * uni (* sa: K : kind  or           *)

  and ancestor = Anc of cid option * int * cid option

  (* Structure declaration *)
  type strDec = StrDec of string * mid option
  [@@deriving eq, ord, show { with_path = false }]

  (* Form of constant declaration:
      from constraint domain | ordinary declaration | %clause declaration *)
  type conDecForm = FromCS | Ordinary | Clause
  [@@deriving eq, ord, show { with_path = false }]

  (* Type abbreviations: G = . | G,D *)
  type nonrec dctx = dec ctx

  (* Us = U[s] *)
  type nonrec eclo = exp * sub

  (* Bs = B[s] *)
  type nonrec bclo = block * sub

  (* constraints *)
  type nonrec cnstr = cnstr_ ref

  (*  exception Error of string              raised if out of space      *)
  module FgnExpStd = struct
    module ToInternal = FgnOpnTable (struct
      type nonrec arg = unit
      type nonrec result = exp
    end)

    module Map = FgnOpnTable (struct
      type nonrec arg = exp -> exp
      type nonrec result = exp
    end)

    module App = FgnOpnTable (struct
      type nonrec arg = exp -> unit
      type nonrec result = unit
    end)

    module EqualTo = FgnOpnTable (struct
      type nonrec arg = exp
      type nonrec result = bool
    end)

    module UnifyWith = FgnOpnTable (struct
      type nonrec arg = dec ctx * exp
      type nonrec result = fgnUnify
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
      type nonrec result = (dec ctx * exp) list
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
    let sgnArray = (Array.array (maxCid + 1, dummyEntry) : conDec Array.array)
    let nextCid = ref 0
    let maxMid = Global.maxMid

    let sgnStructArray =
      (Array.array (maxMid + 1, StrDec ("", None)) : strDec Array.array)

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
  (* roughly 15% on standard suite for Stelf 1.1 *)
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
  (* roughly 15% on standard suite for Stelf 1.1 *)
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
