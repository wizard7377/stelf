open Global
open Common


(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)
module Make_Ast (Common : Common.COMMON) :
  Ast_intf.AST with module Common = Common = struct
  module Common = Common
  open Common
  type cid = Cid.t
  (** Constant identifier *)
 
  let equal_cid = Cid.equal 
  let compare_cid = Cid.compare 
  let pp_cid = Cid.pp 
  let show_cid = Cid.show

  type nonrec name = string 
  (** Variable name *)

  let equal_name (a : name) b = a = b
  let compare_name (a : name) b = compare a b
  let pp_name = Format.pp_print_string
  let show_name s = s

  type mid = Mid.t [@@deriving eq, ord, show]
  (** Structure identifier *)

  type csid = cid [@@deriving eq, ord, show]
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
  let ctxPop = function
    | Decl (g_, _) -> g_
    | Null -> invalid_arg "ctxPop: empty context"

  exception Error of string

  (* raised if out of space     *)
  (* ctxLookup (G, k) = D, kth declaration in G from right to left
     Invariant: 1 <= k <= |G|, where |G| is length of G
  *)
  let rec ctxLookup = function
    | Decl (_, d_), 1 -> d_
    | Decl (g'_, _), k' -> ctxLookup (g'_, k' - 1)
    | Null, _ -> invalid_arg "ctxLookup: out of bounds"

  (*    | ctxLookup (Null, k') = (print (""Looking up k' = "" ^ Int.toString k' ^ ""\n""); raise Error ""Out of Bounce\n"")*)
  (* ctxLookup (Null, k')  should not occur by invariant *)
  (* ctxLength G = |G|, the number of declarations in G *)
  let ctxLength g_ =
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
    | Tag of
      (Tag.t
       [@equal fun _ _ -> true]
       [@compare fun _ _ -> 0]
       [@printer fun fmt _ -> Format.pp_print_string fmt "<tag>"])
      * exp
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

  let arrow_ (a, b) = Pi ((Dec (None, a), No), b)

  let conDecName = function
    | ConDec (name, _, _, _, _, _)
    | ConDef (name, _, _, _, _, _, _)
    | AbbrevDef (name, _, _, _, _, _)
    | BlockDec (name, _, _, _)
    | BlockDef (name, _, _)
    | SkoDec (name, _, _, _, _) -> name

  let conDecParent = function
    | ConDec (_, parent, _, _, _, _)
    | ConDef (_, parent, _, _, _, _, _)
    | AbbrevDef (_, parent, _, _, _, _)
    | BlockDec (_, parent, _, _)
    | BlockDef (_, parent, _)
    | SkoDec (_, parent, _, _, _) -> parent

  let conDecImp = function
    | ConDec (_, _, imp, _, _, _)
    | ConDef (_, _, imp, _, _, _, _)
    | AbbrevDef (_, _, imp, _, _, _)
    | SkoDec (_, _, imp, _, _) -> imp
    | BlockDec _
    | BlockDef _ -> 0

  let conDecStatus = function
    | ConDec (_, _, _, status, _, _) -> status
    | _ -> Normal

  let conDecType = function
    | ConDec (_, _, _, _, exp, _)
    | ConDef (_, _, _, _, exp, _, _)
    | AbbrevDef (_, _, _, _, exp, _)
    | SkoDec (_, _, _, exp, _) -> exp
    | _ -> assert false

  let conDecBlock = function
    | BlockDec (_, _, g, ds) -> (g, ds)
    | _ -> assert false

  let conDecUni = function
    | ConDec (_, _, _, _, _, uni)
    | ConDef (_, _, _, _, _, uni, _)
    | AbbrevDef (_, _, _, _, _, uni)
    | SkoDec (_, _, _, _, uni) -> uni
    | _ -> assert false

  let strDecName = function
    | StrDec (name, _) -> name

  let strDecParent = function
    | StrDec (_, parent) -> parent

  end 
