open! Intsyn.Lambda_
open! Print.Print_

(* # 1 "src/compile/Assign.sig.ml" *)

(* Assignment *)
(* Author: Larry Greenfield *)
(* Modified: Brigitte Pientka *)
include ASSIGN
(* signature ASSIGN *)

(* # 1 "src/compile/Assign.fun.ml" *)
open! Basis

(* Assignment *)
(* Author: Brigitte Pientka *)
exception Assignment of string

let () =
  Printexc.register_printer (function Assignment msg -> Some msg | _ -> None)

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

  exception Assignment = Assignment

  open! struct
    open IntSyn

    let rec assignExpW (g, a, b, cnstr) = match a, b with
      | (Uni l1, _), (Uni l2, _) -> cnstr
      | ((Root (h1, s1_), s1) as us1), ((Root (h2, s2_), s2) as us2) ->
          begin match (h1, h2) with
          | Const c1, Const c2 ->
              begin if c1 = c2 then assignSpine (g, (s1_, s1), (s2_, s2), cnstr)
              else raise (Assignment "Constant clash")
              end
          | BVar k1, BVar k2 ->
              begin if k1 = k2 then assignSpine (g, (s1_, s1), (s2_, s2), cnstr)
              else raise (Assignment "Bound variable clash")
              end
          | Skonst c1, Skonst c2 ->
              begin if c1 = c2 then assignSpine (g, (s1_, s1), (s2_, s2), cnstr)
              else raise (Assignment "Skolem constant clash")
              end
          | Def d1, Def d2 ->
              begin if d1 = d2 then assignSpine (g, (s1_, s1), (s2_, s2), cnstr)
              else assignExp (g, Whnf.expandDef us1, Whnf.expandDef us2, cnstr)
              end
          | Def d1, _ -> assignExp (g, Whnf.expandDef us1, us2, cnstr)
          | _, Def d2 -> assignExp (g, us1, Whnf.expandDef us2, cnstr)
          | ( FgnConst (cs1, ConDec (n1, _, _, _, _, _)),
              FgnConst (cs2, ConDec (n2, _, _, _, _, _)) ) ->
              begin if cs1 = cs2 && n1 = n2 then cnstr
              else raise (Assignment "Foreign Constant clash")
              end
          | ( FgnConst (cs1, ConDef (n1, _, _, w1, _, _, _)),
              FgnConst (cs2, ConDef (n2, _, _, v, w2, _, _)) ) ->
              begin if cs1 = cs2 && n1 = n2 then cnstr
              else assignExp (g, (w1, s1), (w2, s2), cnstr)
              end
          | FgnConst (_, ConDef (_, _, _, w1, _, _, _)), _ ->
              assignExp (g, (w1, s1), us2, cnstr)
          | _, FgnConst (_, ConDef (_, _, _, w2, _, _, _)) ->
              assignExp (g, us1, (w2, s2), cnstr)
          | _ -> raise (Assignment "Head mismatch ")
          end
      | (Lam (d1, u1), s1), (Lam (d2, u2), s2) ->
          assignExp
            (Decl (g, decSub d1 s1), (u1, dot1 s1), (u2, dot1 s2), cnstr)
      | (u1, s1), (Lam (d2, u2), s2) ->
          assignExp
            ( Decl (g, decSub d2 s2),
              (Redex (EClo (u1, shift), App (Root (BVar 1, Nil), Nil)), dot1 s1),
              (u2, dot1 s2),
              cnstr )
      | (Pi (((Dec (_, v1) as d1), _), u1), s1), (Pi (((Dec (_, v2) as d2), _), u2), s2) ->
          let cnstr' = assignExp (g, (v1, s1), (v2, s2), cnstr) in
          assignExp
            (Decl (g, decSub d1 s1), (u1, dot1 s1), (u2, dot1 s2), cnstr')
      | ((u, s1) as us1), ((EVar (r2, _, _, _), s2) as us2) -> begin
          r2 := Some (EClo (fst us1, snd us1));
          cnstr
        end
      | ((u, s1) as us1), ((AVar r2, s2) as us2) -> begin
          r2 := Some (EClo (fst us1, snd us1));
          cnstr
        end
      | (Lam (d1, u1), s1), (u2, s2) ->
          assignExp
            ( Decl (g, decSub d1 s1),
              (u1, dot1 s1),
              (Redex (EClo (u2, shift), App (Root (BVar 1, Nil), Nil)), dot1 s2),
              cnstr )
      | us1, ((EClo (u, s'), s) as us2) ->
          assignExp (g, us1, (u, comp s' s), cnstr)
      | ((EVar (r, _, v, cnstr_), s) as us1), us2 ->
          Eqn (g, EClo (fst us1, snd us1), EClo (fst us2, snd us2)) :: cnstr
      | ((EClo (u, s'), s) as us1), us2 ->
          assignExp (g, (u, comp s' s), us2, cnstr)
      | ((FgnExp (_, fe), _) as us1), us2 ->
          Eqn (g, EClo (fst us1, snd us1), EClo (fst us2, snd us2)) :: cnstr
      | us1, ((FgnExp (_, fe), _) as us2) ->
          Eqn (g, EClo (fst us1, snd us1), EClo (fst us2, snd us2)) :: cnstr

    and assignSpine (g, a, b, cnstr) = match a, b with
      | (Nil, _), (Nil, _) -> cnstr
      | (SClo (s1_, s1'), s1), ss ->
          assignSpine (g, (s1_, comp s1' s1), ss, cnstr)
      | ss, (SClo (s2_, s2'), s2) ->
          assignSpine (g, ss, (s2_, comp s2' s2), cnstr)
      | (App (u1, s1_), s1), (App (u2, s2_), s2) ->
          let cnstr' = assignExp (g, (u1, s1), (u2, s2), cnstr) in
          assignSpine (g, (s1_, s1), (s2_, s2), cnstr')

    and assignExp (g, us1, ((u2, s2) as us2), cnstr) =
      assignExpW (g, Whnf.whnf us1, Whnf.whnf us2, cnstr)

    let rec solveCnstr = function
      | [] -> true
      | Eqn (g, u1, u2) :: cnstr ->
          Unify.unifiable g (u1, id) (u2, id) && solveCnstr cnstr

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
      | Dot (Undef, s) -> begin
          print "Undef . ";
          printSub s
        end

    let unifyW a3 b3 c3 = match a3, b3, c3 with
      | g, ((AVar ({ contents = None } as r) as xs1), s), us2 ->
          r := Some (EClo (fst us2, snd us2))
      | g, xs1, us2 -> Unify.unifyW g xs1 us2

    let unify g xs1 us2 = unifyW g (Whnf.whnf xs1) (Whnf.whnf us2)

    let matchW a3 b3 c3 = match a3, b3, c3 with
      | g, ((AVar ({ contents = None } as r) as xs1), s), us2 ->
          r := Some (EClo (fst us2, snd us2))
      | g, xs1, us2 -> Match.matchW g xs1 us2

    let match_ (g, xs1, us2) = matchW g (Whnf.whnf xs1) (Whnf.whnf us2)
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

  let unifiable g us1 us2 =
    try
      begin
        unify g us1 us2;
        true
      end
    with Unify.Unify msg -> false

  let instance g us1 us2 =
    try
      begin
        match_ (g, us1, us2);
        true
      end
    with Match.Match msg -> false

  (*
    fun assign(G, Us1, Us2) = assignExp(G, Us1, Us2, [])
    *)
  let assignable g us1 uts2 =
    try Some (assignExp (g, us1, uts2, [])) with Assignment msg -> None

  let firstConstArg (IntSyn.Root ((IntSyn.Const c as h), s_) as a_) s =
    let i = IntSyn.conDecImp (IntSyn.sgnLookup c) in
    let rec constExp (u, s) = constExpW (Whnf.whnf (u, s))
    and constExpW (a, s) = match a with
      | IntSyn.Lam (d, u) -> constExp (u, s)
      | IntSyn.Root ((IntSyn.Const cid as h), s) -> Some cid
      | _ -> None
    in
    let rec ithElem (k, a) = match a with
      | (IntSyn.App (u, s_), s) ->
          begin if k = i then constExp (u, s) else ithElem (k + 1, (s_, s))
          end
      | (Nil, s) -> None
    in
    ithElem (0, (s_, s))
  (* #implicit arguments to predicate *)
  (* other cases cannot occur during compilation *)
end
(*! sharing Print.IntSyn = IntSyn' !*)
(* functor Assign *)

(* # 1 "src/compile/Assign.sml.ml" *)
