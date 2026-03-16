(* # 1 "src/compile/assign.sig.ml" *)
open! Basis

(* Assignment *)
(* Author: Larry Greenfield *)
(* Modified: Brigitte Pientka *)
module type ASSIGN = sig
  (*! structure IntSyn : INTSYN !*)
  (* assignable (Us,ps) assigns the term U[s] to the 
     linear higher-order pattern p[s]; if successfull it
     returns a list of residual equations that have been postponed *)
  (* EVars and AVars in ps are instantiated as an effect *)
  val assignable :
    IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> IntSyn.cnstr_ list option

  (* solveCnstr solves dynamically residuated equations *)
  val solveCnstr : IntSyn.cnstr_ list -> bool

  (* unifiable solves statically residuated equations *)
  val unifiable : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool

  (* instance solves statically residuated equations *)
  val instance : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool
  val firstConstArg : IntSyn.exp * IntSyn.sub -> IntSyn.cid option
end
(* signature ASSIGN *)

(* # 1 "src/compile/assign.fun.ml" *)
open! Basis

(* Assignment *)
(* Author: Brigitte Pientka *)
module Assign (Assign__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn' !*)
  module Print : PRINT
end) : ASSIGN = struct
  (*! structure IntSyn = IntSyn' !*)
  open Assign__0

  exception Assignment of string

  open! struct
    open IntSyn

    let rec assignExpW = function
      | g_, (Uni l1_, _), (Uni l2_, _), cnstr -> cnstr
      | ( g_,
          ((Root (h1_, s1_), s1) as us1_),
          ((Root (h2_, s2_), s2) as us2_),
          cnstr ) -> begin
          match (h1_, h2_) with
          | Const c1, Const c2 -> begin
              if c1 = c2 then assignSpine (g_, (s1_, s1), (s2_, s2), cnstr)
              else raise (Assignment "Constant clash")
            end
          | BVar k1, BVar k2 -> begin
              if k1 = k2 then assignSpine (g_, (s1_, s1), (s2_, s2), cnstr)
              else raise (Assignment "Bound variable clash")
            end
          | Skonst c1, Skonst c2 -> begin
              if c1 = c2 then assignSpine (g_, (s1_, s1), (s2_, s2), cnstr)
              else raise (Assignment "Skolem constant clash")
            end
          | Def d1, Def d2 -> begin
              if d1 = d2 then assignSpine (g_, (s1_, s1), (s2_, s2), cnstr)
              else
                assignExp (g_, Whnf.expandDef us1_, Whnf.expandDef us2_, cnstr)
            end
          | Def d1, _ -> assignExp (g_, Whnf.expandDef us1_, us2_, cnstr)
          | _, Def d2 -> assignExp (g_, us1_, Whnf.expandDef us2_, cnstr)
          | ( FgnConst (cs1, ConDec (n1, _, _, _, _, _)),
              FgnConst (cs2, ConDec (n2, _, _, _, _, _)) ) -> begin
              if cs1 = cs2 && n1 = n2 then cnstr
              else raise (Assignment "Foreign Constant clash")
            end
          | ( FgnConst (cs1, ConDef (n1, _, _, w1_, _, _, _)),
              FgnConst (cs2, ConDef (n2, _, _, v_, w2_, _, _)) ) -> begin
              if cs1 = cs2 && n1 = n2 then cnstr
              else assignExp (g_, (w1_, s1), (w2_, s2), cnstr)
            end
          | FgnConst (_, ConDef (_, _, _, w1_, _, _, _)), _ ->
              assignExp (g_, (w1_, s1), us2_, cnstr)
          | _, FgnConst (_, ConDef (_, _, _, w2_, _, _, _)) ->
              assignExp (g_, us1_, (w2_, s2), cnstr)
          | _ -> raise (Assignment "Head mismatch ")
        end
      | g_, (Lam (d1_, u1_), s1), (Lam (d2_, u2_), s2), cnstr ->
          assignExp
            (Decl (g_, decSub (d1_, s1)), (u1_, dot1 s1), (u2_, dot1 s2), cnstr)
      | g_, (u1_, s1), (Lam (d2_, u2_), s2), cnstr ->
          assignExp
            ( Decl (g_, decSub (d2_, s2)),
              (Redex (EClo (u1_, shift), App (Root (BVar 1, Nil), Nil)), dot1 s1),
              (u2_, dot1 s2),
              cnstr )
      | ( g_,
          (Pi (((Dec (_, v1_) as d1_), _), u1_), s1),
          (Pi (((Dec (_, v2_) as d2_), _), u2_), s2),
          cnstr ) ->
          let cnstr' = assignExp (g_, (v1_, s1), (v2_, s2), cnstr) in
          assignExp
            (Decl (g_, decSub (d1_, s1)), (u1_, dot1 s1), (u2_, dot1 s2), cnstr')
      | g_, ((u_, s1) as us1_), ((EVar (r2, _, _, _), s2) as us2_), cnstr ->
        begin
          r2 := Some (EClo (fst us1_, snd us1_));
          cnstr
        end
      | g_, ((u_, s1) as us1_), ((AVar r2, s2) as us2_), cnstr -> begin
          r2 := Some (EClo (fst us1_, snd us1_));
          cnstr
        end
      | g_, (Lam (d1_, u1_), s1), (u2_, s2), cnstr ->
          assignExp
            ( Decl (g_, decSub (d1_, s1)),
              (u1_, dot1 s1),
              (Redex (EClo (u2_, shift), App (Root (BVar 1, Nil), Nil)), dot1 s2),
              cnstr )
      | g_, us1_, ((EClo (u_, s'), s) as us2_), cnstr ->
          assignExp (g_, us1_, (u_, comp (s', s)), cnstr)
      | g_, ((EVar (r, _, v_, cnstr_), s) as us1_), us2_, cnstr ->
          Eqn (g_, EClo (fst us1_, snd us1_), EClo (fst us2_, snd us2_))
          :: cnstr
      | g_, ((EClo (u_, s'), s) as us1_), us2_, cnstr ->
          assignExp (g_, (u_, comp (s', s)), us2_, cnstr)
      | g_, ((FgnExp (_, fe), _) as us1_), us2_, cnstr ->
          Eqn (g_, EClo (fst us1_, snd us1_), EClo (fst us2_, snd us2_))
          :: cnstr
      | g_, us1_, ((FgnExp (_, fe), _) as us2_), cnstr ->
          Eqn (g_, EClo (fst us1_, snd us1_), EClo (fst us2_, snd us2_))
          :: cnstr

    and assignSpine = function
      | g_, (Nil, _), (Nil, _), cnstr -> cnstr
      | g_, (SClo (s1_, s1'), s1), ss_, cnstr ->
          assignSpine (g_, (s1_, comp (s1', s1)), ss_, cnstr)
      | g_, ss_, (SClo (s2_, s2'), s2), cnstr ->
          assignSpine (g_, ss_, (s2_, comp (s2', s2)), cnstr)
      | g_, (App (u1_, s1_), s1), (App (u2_, s2_), s2), cnstr ->
          let cnstr' = assignExp (g_, (u1_, s1), (u2_, s2), cnstr) in
          assignSpine (g_, (s1_, s1), (s2_, s2), cnstr')

    and assignExp (g_, us1_, ((u2_, s2) as us2_), cnstr) =
      assignExpW (g_, Whnf.whnf us1_, Whnf.whnf us2_, cnstr)

    let rec solveCnstr = function
      | [] -> true
      | Eqn (g_, u1_, u2_) :: cnstr_ ->
          Unify.unifiable (g_, (u1_, id), (u2_, id)) && solveCnstr cnstr_

    let rec printSub = function
      | Shift n -> print (("Shift " ^ Int.toString n) ^ "\n")
      | Dot (Idx n, s) -> begin
          print (("Idx " ^ Int.toString n) ^ " . ");
          printSub s
        end
      | Dot (Exp (EVar (_, _, _, _)), s) -> begin
          print "Exp (EVar _ ). ";
          printSub s
        end
      | Dot (Exp (AVar _), s) -> begin
          print "Exp (AVar _ ). ";
          printSub s
        end
      | Dot (Exp (EClo (AVar _, _)), s) -> begin
          print "Exp (AVar _ ). ";
          printSub s
        end
      | Dot (Exp (EClo (_, _)), s) -> begin
          print "Exp (EClo _ ). ";
          printSub s
        end
      | Dot (Exp _, s) -> begin
          print "Exp (_ ). ";
          printSub s
        end
      | Dot (undef_, s) -> begin
          print "Undef . ";
          printSub s
        end

    let rec unifyW = function
      | g_, ((AVar ({ contents = None } as r) as xs1_), s), us2_ ->
          r := Some (EClo (fst us2_, snd us2_))
      | g_, xs1_, us2_ -> Unify.unifyW (g_, xs1_, us2_)

    let rec unify (g_, xs1_, us2_) = unifyW (g_, Whnf.whnf xs1_, Whnf.whnf us2_)

    let rec matchW = function
      | g_, ((AVar ({ contents = None } as r) as xs1_), s), us2_ ->
          r := Some (EClo (fst us2_, snd us2_))
      | g_, xs1_, us2_ -> Match.matchW (g_, xs1_, us2_)

    let rec match_ (g_, xs1_, us2_) = matchW (g_, Whnf.whnf xs1_, Whnf.whnf us2_)
  end

  (*
     templates
           p ::= Root(n, NIL) | Root(c, SP) | EVar (X, V) | AVar A |
                 Lam (D, p)
                   where X is uninstantiated and occurs uniquely
                   any multiple occurrence of X has been renamed to A.

                 any eta-expanded EVar remains an EVar
                 but it may be lowered during whnf (or in the special case here
                 expansion)

          SP ::= p ; SP | NIL

   *)
  (* assignExpW (G, (U1, s1), (U2, s2)) = ()

     invariant:
     G |- s1 : G1    G1 |- U1 : V1   (U1, s1) in whnf
     G |- s2 : G2    G2 |- U2 : V2   (U2, s2) is template
  *)
  (* L1 = L2 by invariant *)
  (* cannot occur by invariant; all definitions in clause heads have been
               replaced by AVars Tue Jun 18 19:47:39 2002 -bp *)
  (* because of strict *)
  (* cannot occur by invariant; all definitions in clause heads have been
               replaced by AVars Tue Jun 18 19:47:44 2002 -bp *)
  (* we require unique string representation of external constants *)
  (* D1[s1] = D2[s2]  by invariant *)
  (* Cannot occur if expressions are eta expanded *)
  (* same reasoning holds as above *)
  (* s2 = id *)
  (* don't trail, because EVar has been created since most recent choice point *)
  (* Tue Apr  2 10:23:19 2002 -bp -fp *)
  (* s2 = id *)
  (* don't trail, because AVars never survive local scope *)
  (* ETA: can't occur if eta expanded *)
  (* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                        = (U2 [^] 1) [1.s2 o ^] *)
  (* by invariant Us2 cannot contain any FgnExp *)
  (* s = id *)
  (* Xs1 should not contain any uninstantiated AVar anymore *)
  (* s = id *)
  (* Xs1 should not contain any uninstantiated AVar anymore *)
  let solveCnstr = solveCnstr

  let rec unifiable (g_, us1_, us2_) =
    try
      begin
        unify (g_, us1_, us2_);
        true
      end
    with Unify.Unify msg -> false

  let rec instance (g_, us1_, us2_) =
    try
      begin
        match_ (g_, us1_, us2_);
        true
      end
    with Match.Match msg -> false

  (*
    fun assign(G, Us1, Us2) = assignExp(G, Us1, Us2, [])
    *)
  let rec assignable (g_, us1_, uts2_) =
    try Some (assignExp (g_, us1_, uts2_, [])) with Assignment msg -> None

  let rec firstConstArg ((IntSyn.Root ((IntSyn.Const c as h), s_) as a_), s) =
    let i = IntSyn.conDecImp (IntSyn.sgnLookup c) in
    let rec constExp (u_, s) = constExpW (Whnf.whnf (u_, s))
    and constExpW = function
      | IntSyn.Lam (d_, u_), s -> constExp (u_, s)
      | IntSyn.Root ((IntSyn.Const cid as h_), s_), s -> Some cid
      | _, _ -> None
    in
    let rec ithElem = function
      | k, (IntSyn.App (u_, s_), s) -> begin
          if k = i then constExp (u_, s) else ithElem (k + 1, (s_, s))
        end
      | k, (Nil, s) -> None
    in
    ithElem (0, (s_, s))
  (* #implicit arguments to predicate *)
  (* other cases cannot occur during compilation *)
end
(*! sharing Print.IntSyn = IntSyn' !*)
(* functor Assign *)

(* # 1 "src/compile/assign.sml.ml" *)
