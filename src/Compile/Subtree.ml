open! Global.Global_
open! Table
open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Formatter__Formatter_
open! Solvers.Solvers_

(* # 1 "src/compile/Subtree.sig.ml" *)

(* Substitution Trees *)
(* Author: Brigitte Pientka *)
include SUBTREE

(*  val goalToString : string -> IntSyn.Dec IntSyn.Ctx * CompSyn.Goal * IntSyn.Sub -> string *)
(* signature SUBTREE *)

(* # 1 "src/compile/Subtree.fun.ml" *)
open! Basis

(* Substitution Tree indexing *)
(* Author: Brigitte Pientka *)
module SubTree (SubTree__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*!structure CompSyn' : COMPSYN !*)
  (*!  sharing CompSyn'.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*!  sharing Whnf.IntSyn = IntSyn' !*)
  module Unify : UNIFY

  (*!  sharing Unify.IntSyn = IntSyn'!*)
  module Print : PRINT

  (*!  sharing Print.IntSyn = IntSyn' !*)
  (* CPrint currently unused *)
  module CPrint : Cprint.CPRINT

  (*!  sharing CPrint.IntSyn = IntSyn' !*)
  (*!  sharing CPrint.CompSyn = CompSyn' !*)
  (* unused *)
  module Formatter : FORMATTER

  (*!  sharing Print.Formatter = Formatter !*)
  (* unused *)
  module Names : NAMES

  (*!  sharing Names.IntSyn = IntSyn' !*)
  module CsManager : CsManager.CS_MANAGER
end) : SUBTREE = struct
  open SubTree__0

  (*!  structure IntSyn = IntSyn' !*)
  (*!  structure CompSyn = CompSyn' !*)
  (*!  structure RBSet = RBSet !*)
  type nonrec nvar = int

  (* index for normal variables *)
  type nonrec bvar = int

  (* index for bound variables *)
  type nonrec bdepth = int

  (* depth of locally bound variables *)
  (* A substitution tree is defined as follows:
     Node := Leaf (ns, G, sgoal) | Node(ns, Set of Nodes)
     normal linear modal substitutions ns := . | R/n, ns

   For each node we have the following invariant:
        S |- ns : S'    i.e. ns substitutes for internal variables
        G'|- as : G     i.e. as substitutes for assignable variables
        G |- qs : G     i.e. qs substitutes for modal variables
                             occuring in the query term

  NOTE: Since lambda-abstraction carries a type-label, we must generalize
   the type-label, and hence perform indexing on type-labels. -- On
   the other hand during unification or assignment an instantiation of
   the existential variables occurring in the type-label is not
   necessary. They must have been instantiated already. However, we
   must still instantiate internal nvars.

  Example: given the following two terms:
   hilnd ((A imp (B imp C)) imp ((A imp B) imp (A imp C))) (s) (impi [u:nd (A imp B imp C)]
                     impi [v:nd (A imp B)]
                     impi [w:nd A] impe (impe u w) (impe v w)).

   hilnd (A imp (B imp A)) (s) (impi [u:nd A]
                     impi [v:nd B]
                     impi [w:nd A] impe (impe u w) (impe v w)).


  if we generalize (A imp B imp C) then we must obtain

  hilnd (n1 imp (n2 imp n3)) (s) (impi [u:nd n4]
             impi [v:nd n5]
             impi [w:nd A] impe (impe u w) (impe v w)).

  otherwise we could obtain a term which is not well-typed.

  *)
  (* typeLabel distinguish between declarations (=type labels)
   which are subject to indexing, but only the internal nvars will
   be instantiated during asssignment and Body which are subject to
   indexing and existential variables and nvars will be instantiated
   during assignment
 *)
  type typeLabel = TypeLabel | Body [@@deriving eq, ord, show]
  type nonrec normalSubsts = (typeLabel * IntSyn.exp) RedBlackSet.RBSet.ordSet

  (* key = int = bvar *)
  type assSub = Assign of IntSyn.dec IntSyn.ctx * IntSyn.exp
  type nonrec assSubsts = assSub RedBlackSet.RBSet.ordSet

  (* key = int = bvar *)
  type nonrec querySubsts =
    (IntSyn.dec IntSyn.ctx * (typeLabel * IntSyn.exp)) RedBlackSet.RBSet.ordSet

  type cnstr = Eqn of IntSyn.dec IntSyn.ctx * IntSyn.exp * IntSyn.exp
  type nonrec cnstrSubsts = IntSyn.exp RedBlackSet.RBSet.ordSet

  (* key = int = bvar *)
  type cGoal =
    | CGoals of
        CompSyn.CompSyn.auxGoal * IntSyn.cid * CompSyn.CompSyn.conjunction * int

  (* cid of clause *)
  type genType = Top | Regular [@@deriving eq, ord, show]

  type tree =
    | Leaf of normalSubsts * IntSyn.dec IntSyn.ctx * cGoal
    | Node of normalSubsts * tree RedBlackSet.RBSet.ordSet

  type nonrec candidate =
    assSubsts
    * normalSubsts
    * cnstrSubsts
    * cnstr
    * IntSyn.dec IntSyn.ctx
    * cGoal

  (* Initialization of substitutions *)
  let nid : unit -> normalSubsts = RedBlackSet.RBSet.new_
  let assignSubId : unit -> assSubsts = RedBlackSet.RBSet.new_
  let cnstrSubId : unit -> cnstrSubsts = RedBlackSet.RBSet.new_
  let querySubId : unit -> querySubsts = RedBlackSet.RBSet.new_

  (* Identity substitution *)
  let isId s = RedBlackSet.RBSet.isEmpty s

  (* Initialize substitution tree *)
  let makeTree () = ref (Node (nid (), RedBlackSet.RBSet.new_ ()))

  (* Test if node has any children *)
  let noChildren c = RedBlackSet.RBSet.isEmpty c

  (* Index array

   Invariant:
   For all type families  a  indexArray = [a1,...,an]
   where a1,...,an is a substitution tree consisting of all constants
   for target family ai

   *)
  let indexArray =
    Array.tabulate (Global.maxCid, function i -> (ref 0, makeTree ()))

  open! struct
    module I = IntSyn
    module C = CompSyn.CompSyn
    module S = RedBlackSet.RBSet

    exception Error of string
    exception Assignment of string
    exception Generalization of string

    let cidFromHead = function I.Const c -> c | I.Def c -> c
    let rec dotn (i, s) = match i with 0 -> s | i -> dotn (i - 1, I.dot1 s)

    let rec compose' = function
      | I.Null, g -> g
      | IntSyn.Decl (g, d), g' -> IntSyn.Decl (compose' (g, g'), d)

    let rec shift (a, s) = match a with
      | I.Null -> s
      | IntSyn.Decl (g, d) -> I.dot1 (shift (g, s))

    let rec raiseType a2 b2 = match a2, b2 with
      | I.Null, v -> v
      | I.Decl (g, d), v -> raiseType g (I.Lam (d, v))

    let rec printSub = function
      | IntSyn.Shift n -> print (("Shift " ^ Int.toString n) ^ "\n")
      | IntSyn.Dot (IntSyn.Idx n, s) -> begin
          print (("Idx " ^ Int.toString n) ^ " . ");
          printSub s
        end
      | IntSyn.Dot (IntSyn.Exp (IntSyn.EVar (_, _, _, _)), s) -> begin
          print "Exp (EVar _ ). ";
          printSub s
        end
      | IntSyn.Dot (IntSyn.Exp (IntSyn.AVar _), s) -> begin
          print "Exp (AVar _ ). ";
          printSub s
        end
      | IntSyn.Dot (IntSyn.Exp (IntSyn.EClo (IntSyn.AVar _, _)), s) -> begin
          print "Exp (AVar _ ). ";
          printSub s
        end
      | IntSyn.Dot (IntSyn.Exp (IntSyn.EClo (_, _)), s) -> begin
          print "Exp (EClo _ ). ";
          printSub s
        end
      | IntSyn.Dot (IntSyn.Exp _, s) -> begin
          print "Exp (_ ). ";
          printSub s
        end
      | IntSyn.Dot (IntSyn.Undef, s) -> begin
          print "Undef . ";
          printSub s
        end

    let nctr = ref 1

    let newNVar () =
      begin
        nctr := !nctr + 1;
        I.NVar !nctr
      end

    let eqHeads = function
      | I.Const k, I.Const k' -> k = k'
      | I.BVar k, I.BVar k' -> k = k'
      | I.Def k, I.Def k' -> k = k'
      | _, _ -> false

    let compatible (label, t, u, rho_t, rho_u) =
      let rec genExp (label, b, a, c) = match a, c with
        | (I.NVar n as t), (I.Root (h, s) as u) -> begin
            S.insert rho_u (n, (label, u));
            t
          end
        | (I.Root (h1, s1) as t), (I.Root (h2, s2) as u) ->
            begin if eqHeads (h1, h2) then
              I.Root (h1, genSpine (label, b, s1, s2))
            else
              begin match b with
              | Regular -> begin
                  S.insert rho_t (!nctr + 1, (label, t));
                  begin
                    S.insert rho_u (!nctr + 1, (label, u));
                    newNVar ()
                  end
                end
              | _ -> raise (Generalization "Should never happen!")
              end
            end
        | I.Lam ((I.Dec (n, a1) as d1), t1), I.Lam ((I.Dec (_, a2) as d2), u2) ->
            I.Lam
              ( I.Dec (n, genExp (TypeLabel, Regular, a1, a2)),
                genExp (label, b, t1, u2) )
        | I.Pi (((d1, _no1_) as dd1), e1), I.Pi (((d2, _no2_) as dd2), e2) ->
            I.Pi
              ( (genDec (TypeLabel, Regular, d1, d2), I.No),
                genExp (label, b, e1, e2) )
        | I.Pi (((d1, _maybe1_) as dd1), e1), I.Pi (((d2, _maybe2_) as dd2), e2) ->
            I.Pi
              ( (genDec (TypeLabel, Regular, d1, d2), I.Maybe),
                genExp (label, b, e1, e2) )
        | I.Pi (((d1, _meta1_) as dd1), e1), I.Pi (((d2, _meta2_) as dd2), e2) ->
            I.Pi
              ( (genDec (TypeLabel, Regular, d1, d2), I.Meta),
                genExp (label, b, e1, e2) )
        | t, u ->
            raise
              (Generalization "Cases where U= EVar or EClo should never happen!")
      and genSpine (label, b, a, c) = match a, c with
        | Nil, Nil -> I.Nil
        | I.App (t, s1), I.App (u, s2) ->
            I.App (genExp (label, b, t, u), genSpine (label, b, s1, s2))
      and genDec (label, b, I.Dec (n, e1), I.Dec (n', e2)) =
        I.Dec (n, genExp (label, b, e1, e2))
      in
      let rec genTop (label, a, b) = match a, b with
        | (I.Root (h1, s1) as t), (I.Root (h2, s2) as u) ->
            begin if eqHeads (h1, h2) then
              I.Root (h1, genSpine (label, Regular, s1, s2))
            else raise (Generalization "Top-level function symbol not shared")
            end
        | I.Lam ((I.Dec (n, a1) as d1), t1), I.Lam ((I.Dec (_, a2) as d2), u2) ->
            I.Lam
              ( I.Dec (n, genExp (label, Regular, a1, a2)),
                genTop (label, t1, u2) )
        | _, _ ->
            raise (Generalization "Top-level function symbol not shared")
      in
      try Some (genTop (label, t, u)) with Generalization msg -> None

    let compatibleSub (nsub_t, nsub_e) =
      let sg, rho_t, rho_e = (nid (), nid (), nid ()) in
      ignore (S.forall nsub_e (function nv, (l', e) ->
            begin match S.lookup nsub_t nv with
            | Some (l, t) ->
                begin if l = l' then
                  begin match compatible (l, t, e, rho_t, rho_e) with
                  | None -> begin
                      S.insert rho_t (nv, (l, t));
                      S.insert rho_e (nv, (l, e))
                    end
                  | Some t' -> S.insert sg (nv, (l, t'))
                  end
                else raise (Generalization "Labels don't agree\n")
                end
            | None -> S.insert rho_e (nv, (l', e))
            end));
      begin if isId sg then None else Some (sg, rho_t, rho_e)
      end

    let mkNode (a, sg, rho1, b, rho2) = match a, b with
      | Node (_, children), ((g, rc) as gr) ->
          let c = S.new_ () in
          S.insertList c
            [ (1, Node (rho1, children)); (2, Leaf (rho2, g, rc)) ];
          Node (sg, c)
      | Leaf (_, g1, rc1), ((g2, rc2) as gr) ->
          let c = S.new_ () in
          S.insertList c
            [ (1, Leaf (rho1, g1, rc1)); (2, Leaf (rho2, g2, rc2)) ];
          Node (sg, c)

    let rec compareChild
        ( children,
          (n, child),
          nsub_t,
          nsub_e,
          ((g_clause2, res_clause2) as gr) ) =
      begin match compatibleSub (nsub_t, nsub_e) with
      | None ->
          S.insert children (n + 1, Leaf (nsub_e, g_clause2, res_clause2))
      | Some (sg, rho1, rho2) ->
          begin if isId rho1 then
            begin if isId rho2 then
              S.insertShadow children (n, mkNode (child, sg, rho1, gr, rho2))
            else S.insertShadow children (n, insert (child, rho2, gr))
            end
          else S.insertShadow children (n, mkNode (child, sg, rho1, gr, rho2))
          end
      end

    and insert (a, nsub_e, b) = match a, b with
      | (Leaf (nsub_t, g_clause1, r1) as n), ((g_clause2, r2) as gr) ->
          begin match compatibleSub (nsub_t, nsub_e) with
          | None -> raise (Error "Leaf is not compatible substitution r")
          | Some (sg, rho1, rho2) -> mkNode (n, sg, rho1, gr, rho2)
          end
      | (Node (_, children) as n_), ((g_clause2, rc) as gr) ->
          begin if noChildren children then begin
            S.insert children (1, Leaf (nsub_e, g_clause2, rc));
            n_
          end
          else
            begin match S.last children with
            | n, (Node (nsub_t, children') as child) -> begin
                compareChild (children, (n, child), nsub_t, nsub_e, gr);
                n_
              end
            | n, (Leaf (nsub_t, g1, rc1) as child) -> begin
                compareChild (children, (n, child), nsub_t, nsub_e, gr);
                n_
              end
            end
          end

    let rec normalizeNExp = function
      | I.NVar n, csub ->
          let a = I.newAVar () in
          S.insert csub (n, a);
          a
      | I.Root (h, s), nsub -> I.Root (h, normalizeNSpine (s, nsub))
      | I.Lam (d, u), nsub ->
          I.Lam (normalizeNDec (d, nsub), normalizeNExp (u, nsub))
      | I.Pi ((d, p), u), nsub ->
          I.Pi ((normalizeNDec (d, nsub), p), normalizeNExp (u, nsub))

    and normalizeNSpine (a, nsub) = match a with
      | I.Nil -> I.Nil
      | I.App (u, s) ->
          I.App (normalizeNExp (u, nsub), normalizeNSpine (s, nsub))

    and normalizeNDec (I.Dec (n, e), nsub) =
      I.Dec (n, normalizeNExp (e, nsub))

    let assign (nvaronly, glocal_u1, us1, u2, nsub_goal, asub, csub, cnstr) =
      let depth = I.ctxLength glocal_u1 in
      let rec assignHead
          ( nvaronly,
            depth,
            glocal_u1,
            ((I.Root (h1, s1_), s1) as us1),
            (I.Root (h2, s2) as u2),
            cnstr ) =
        begin match (h1, h2) with
        | I.Const c1, I.Const c2 ->
            begin if c1 = c2 then
              assignSpine (nvaronly, depth, glocal_u1, (s1_, s1), s2, cnstr)
            else raise (Assignment "Constant clash")
            end
        | I.Skonst c1, I.Skonst c2 ->
            begin if c1 = c2 then
              assignSpine (nvaronly, depth, glocal_u1, (s1_, s1), s2, cnstr)
            else raise (Assignment "Skolem constant clash")
            end
        | I.Def d1, _ ->
            assignExp
              (nvaronly, depth, glocal_u1, Whnf.expandDef us1, u2, cnstr)
        | ( I.FgnConst (cs1, I.ConDec (n1, _, _, _, _, _)),
            I.FgnConst (cs2, I.ConDec (n2, _, _, _, _, _)) ) ->
            begin if cs1 = cs2 && n1 = n2 then cnstr
            else raise (Assignment "Foreign Constant clash")
            end
        | ( I.FgnConst (cs1, I.ConDef (n1, _, _, w1, _, _, _)),
            I.FgnConst (cs2, I.ConDef (n2, _, _, v, w2, _, _)) ) ->
            begin if cs1 = cs2 && n1 = n2 then cnstr
            else assignExp (nvaronly, depth, glocal_u1, (w1, s1), w2, cnstr)
            end
        | I.FgnConst (_, I.ConDef (_, _, _, w1, _, _, _)), _ ->
            assignExp (nvaronly, depth, glocal_u1, (w1, s1), u2, cnstr)
        | _, I.FgnConst (_, I.ConDef (_, _, _, w2, _, _, _)) ->
            assignExp (nvaronly, depth, glocal_u1, us1, w2, cnstr)
        | _, _ -> raise (Assignment "Head mismatch ")
        end
      and assignExpW (nvaronly, depth, glocal_u1, a, b, cnstr) = match nvaronly, a, b with
        | nvaronly, (I.Uni l1, s1), I.Uni l2 ->
            cnstr
        | nvaronly, us1, I.NVar n -> begin
            let u1, s1 = us1 in
            S.insert nsub_goal (n, (glocal_u1, (nvaronly, I.EClo (u1, s1))));
            cnstr
          end
        | Body, ((I.Root (h1, s1_), s1) as us1), (I.Root (h2, s2) as u2) ->
            begin match h2 with
            | I.BVar k2 ->
                begin if k2 > depth then begin
                  S.insert asub
                    ( k2 - I.ctxLength glocal_u1,
                      Assign (glocal_u1, I.EClo (fst us1, snd us1)) );
                  cnstr
                end
                else
                  begin match h1 with
                  | I.BVar k1 ->
                      begin if k1 = k2 then
                        assignSpine
                          (Body, depth, glocal_u1, (s1_, s1), s2, cnstr)
                      else raise (Assignment "Bound variable clash")
                      end
                  | _ -> raise (Assignment "Head mismatch")
                  end
                end
            | _ -> assignHead (Body, depth, glocal_u1, us1, u2, cnstr)
            end
        | TypeLabel, ((I.Root (h1, s1_), s1) as us1), (I.Root (h2, s2) as u2) ->
            begin match h2 with
            | I.BVar k2 ->
                begin if k2 > depth then cnstr
                else
                  begin match h1 with
                  | I.BVar k1 ->
                      begin if k1 = k2 then
                        assignSpine
                          (TypeLabel, depth, glocal_u1, (s1_, s1), s2, cnstr)
                      else raise (Assignment "Bound variable clash")
                      end
                  | _ -> raise (Assignment "Head mismatch")
                  end
                end
            | _ -> assignHead (TypeLabel, depth, glocal_u1, us1, u2, cnstr)
            end
        | nvaronly, us1, (I.Root (I.BVar k2, s_) as u2) ->
            begin if k2 > depth then
              begin match nvaronly with
              | TypeLabel -> cnstr
              | Body -> begin
                  S.insert asub
                    (k2 - depth, Assign (glocal_u1, I.EClo (fst us1, snd us1)));
                  cnstr
                end
              end
            else
              begin match nvaronly with
              | TypeLabel -> cnstr
              | Body ->
                  begin match us1 with
                  | I.EVar (r, _, v, cnstrs), s ->
                      let u2' = normalizeNExp (u2, csub) in
                      Eqn (glocal_u1, I.EClo (fst us1, snd us1), u2') :: cnstr
                  | I.EClo (u, s'), s ->
                      assignExp
                        ( Body,
                          depth,
                          glocal_u1,
                          (u, I.comp s' s),
                          u2,
                          cnstr )
                  | I.FgnExp (_, ops), _ ->
                      let u2' = normalizeNExp (u2, csub) in
                      Eqn (glocal_u1, I.EClo (fst us1, snd us1), u2') :: cnstr
                  end
              end
            end
        | nvaronly, (I.Lam ((I.Dec (_, a1) as d1), u1), s1), I.Lam ((I.Dec (_, a2) as d2), u2) ->
            let cnstr' =
              assignExp (TypeLabel, depth, glocal_u1, (a1, s1), a2, cnstr)
            in
            assignExp
              ( nvaronly,
                depth + 1,
                I.Decl (glocal_u1, I.decSub d1 s1),
                (u1, I.dot1 s1),
                u2,
                cnstr' )
        | nvaronly, (I.Pi (((I.Dec (_, a1) as d1), _), u1), s1), I.Pi (((I.Dec (_, a2) as d2), _), u2) ->
            let cnstr' =
              assignExp (TypeLabel, depth, glocal_u1, (a1, s1), a2, cnstr)
            in
            assignExp
              ( nvaronly,
                depth + 1,
                I.Decl (glocal_u1, I.decSub d1 s1),
                (u1, I.dot1 s1),
                u2,
                cnstr' )
        | nvaronly, ((I.EVar (r, _, v, cnstrs), s) as us1), u2 ->
            let u2' = normalizeNExp (u2, csub) in
            Eqn (glocal_u1, I.EClo (fst us1, snd us1), u2') :: cnstr
        | nvaronly, ((I.EClo (u, s'), s) as us1), u2
          ->
            assignExp
              (nvaronly, depth, glocal_u1, (u, I.comp s' s), u2, cnstr)
        | nvaronly, ((I.FgnExp (_, ops), _) as us1), u2 ->
            let u2' = normalizeNExp (u2, csub) in
            Eqn (glocal_u1, I.EClo (fst us1, snd us1), u2') :: cnstr
        | nvaronly, us1, (I.FgnExp (_, ops) as u2) ->
            Eqn (glocal_u1, I.EClo (fst us1, snd us1), u2) :: cnstr
      and assignSpine (nvaronly, depth, glocal_u1, a, s, cnstr) = match a, s with
        | (Nil, _), Nil -> cnstr
        | (I.SClo (s1_, s1'), s1), s ->
            assignSpine
              (nvaronly, depth, glocal_u1, (s1_, I.comp s1' s1), s, cnstr)
        | (I.App (u1, s1_), s1), I.App (u2, s2) ->
            let cnstr' =
              assignExp (nvaronly, depth, glocal_u1, (u1, s1), u2, cnstr)
            in
            assignSpine (nvaronly, depth, glocal_u1, (s1_, s1), s2, cnstr')
      and assignExp (nvaronly, depth, glocal_u1, us1, u2, cnstr) =
        assignExpW (nvaronly, depth, glocal_u1, Whnf.whnf us1, u2, cnstr)
      in
      assignExp (nvaronly, depth, glocal_u1, us1, u2, cnstr)

    let assignableLazy
        (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr) =
      let nsub_query' = querySubId () in
      let cref = ref cnstr in
      let assign' (nsub_query, nsub) =
        let nsub_query_left, nsub_left1 =
          S.differenceModulo nsub_query nsub (function glocal_u, (l, u) ->
              (function
              | l', t ->
                  cref :=
                    assign
                      ( l,
                        glocal_u,
                        (u, I.id),
                        t,
                        nsub_query',
                        assignSub,
                        cnstrSub,
                        !cref )))
        in
        let nsub_left' =
          S.update nsub_left1 (function l, u ->
              (l, normalizeNExp (u, cnstrSub)))
        in
        Some
          ( S.union nsub_query_left nsub_query',
            (S.union nsub_left nsub_left', cnstrSub),
            !cref )
      in
      try assign' (nsub_query, nsub) with Assignment msg -> None

    let assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr) =
      let nsub_query' = querySubId () in
      let cref = ref cnstr in
      let assign' (nsub_query, nsub) =
        let nsub_query_left, nsub_left =
          S.differenceModulo nsub_query nsub (function glocal_u, (l, u) ->
              (function
              | l', t ->
                  cref :=
                    assign
                      ( l',
                        glocal_u,
                        (u, I.id),
                        t,
                        nsub_query',
                        assignSub,
                        cnstrSub,
                        !cref )))
        in
        ignore (S.forall nsub_left (function nv, (nvaronly, u) ->
              begin match S.lookup cnstrSub nv with
              | None -> raise (Error "Left-over nsubstitution")
              | Some (I.AVar a) -> a := Some (normalizeNExp (u, cnstrSub))
              end));
        Some (S.union nsub_query_left nsub_query', cnstrSub, !cref)
      in
      try assign' (nsub_query, nsub) with Assignment msg -> None

    let unifyW a3 b3 c3 = match a3, b3, c3 with
      | g, ((I.AVar ({ contents = None } as r) as x), I.Shift 0), us2 ->
          r := Some (I.EClo (fst us2, snd us2))
      | g, ((I.AVar ({ contents = None } as r) as x), s), ((u, s2) as us2) ->
        begin
          print "unifyW -- not s = Id\n";
          begin
            print
              (("Us2 = " ^ Print.expToString g (I.EClo (fst us2, snd us2)))
              ^ "\n");
            r := Some (I.EClo (fst us2, snd us2))
          end
        end
      | g, xs1, us2 -> Unify.unifyW g xs1 us2

    let unify g xs1 us2 = unifyW g (Whnf.whnf xs1) (Whnf.whnf us2)

    let unifiable g us1 us2 =
      try
        begin
          unify g us1 us2;
          true
        end
      with Unify.Unify msg -> false

    let rec ctxToExplicitSub (i, gquery, a, asub) = match a with
      | I.Null -> I.id
      | I.Decl (gclause, I.Dec (_, a)) ->
          let s = ctxToExplicitSub (i + 1, gquery, gclause, asub) in
          let (I.EVar (x', _, _, _) as u') =
            I.newEVar gquery (I.EClo (a, s))
          in
          begin match S.lookup asub i with
          | None -> ()
          | Some (Assign (glocal_u, u)) ->
              x' := Some (raiseType glocal_u u)
          end;
          I.Dot (I.Exp u', s)
      | I.Decl (gclause, I.ADec (_, d)) ->
          let (I.AVar x' as u') = I.newAVar () in
          begin match S.lookup asub i with
          | None -> ()
          | Some (Assign (glocal_u, u)) -> x' := Some u
          end;
          I.Dot
            ( I.Exp (I.EClo (u', I.Shift (-d))),
              ctxToExplicitSub (i + 1, gquery, gclause, asub) )

    let rec solveAuxG (trivial, s, gquery) = match trivial with
      | trivial -> true
      | C.UnifyEq (glocal, e1, n, eqns) ->
          let g = compose' (glocal, gquery) in
          let s' = shift (glocal, s) in
          begin if unifiable g (n, s') (e1, s') then
            solveAuxG (eqns, s, gquery)
          else false
          end

    let rec solveCnstr (gquery, gclause, a, s) = match a with
      | [] -> true
      | Eqn (glocal, u1, u2) :: cnstr ->
          Unify.unifiable
            (compose' (gquery, glocal)) (u1, I.id) (u2, shift (glocal, s))
          && solveCnstr (gquery, gclause, cnstr, s)

    let solveResiduals
        (gquery, gclause, CGoals (auxG, cid, conjGoals, i), asub, cnstr', sc) =
      let s = ctxToExplicitSub (1, gquery, gclause, asub) in
      let success =
        solveAuxG (auxG, s, gquery) && solveCnstr (gquery, gclause, cnstr', s)
      in
      begin if success then sc ((conjGoals, s), cid) else ()
      end

    let ithChild (CGoals (_, _, _, i), n) = i = n

    let retrieveChild (num, child, nsub_query, assignSub, cnstr, gquery, sc) =
      let rec retrieve (a, nsub_query, assignSub, cnstrSub, cnstr) = match a with
        | Leaf (nsub, gclause, residuals) ->
            begin match
              assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr)
            with
            | None -> ()
            | Some (nsub_query', cnstrSub', cnstr') ->
                begin if isId nsub_query' then
                  begin if ithChild (residuals, !num) then
                    solveResiduals
                      (gquery, gclause, residuals, assignSub, cnstr', sc)
                  else
                    CsManager.trail (function () ->
                        solveResiduals
                          (gquery, gclause, residuals, assignSub, cnstr', sc))
                  end
                else raise (Error "Left-over normal substitutions!")
                end
            end
        | Node (nsub, children) ->
            begin match
              assignableEager (nsub, nsub_query, assignSub, cnstrSub, cnstr)
            with
            | None -> ()
            | Some (nsub_query', cnstrSub', cnstr') ->
                S.forall children (function n, child ->
                    retrieve
                      ( child,
                        nsub_query',
                        S.copy assignSub,
                        S.copy cnstrSub',
                        cnstr' ))
            end
      in
      retrieve (child, nsub_query, assignSub, cnstrSubId (), cnstr)

    let retrieval (n, (Node (s, children) as sTree), g, r, sc) =
      let nsub_query, assignSub = (querySubId (), assignSubId ()) in
      S.insert nsub_query (1, (I.Null, (Body, r)));
      S.forall children (function _, c ->
          retrieveChild (n, c, nsub_query, assignSub, [], g, sc))

    let retrieveAll (num, child, nsub_query, assignSub, cnstr, candSet) =
      let i = ref 0 in
      let rec retrieve (a, nsub_query, assignSub, b, cnstr) = match a, b with
        | Leaf (nsub, gclause, residuals), (nsub_left, cnstrSub) ->
            begin match
              assignableLazy
                (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr)
            with
            | None -> ()
            | Some (nsub_query', (nsub_left', cnstrSub'), cnstr') ->
                begin if isId nsub_query' then begin
                  i := !i + 1;
                  begin
                    S.insert candSet
                      ( !i,
                        ( assignSub,
                          nsub_left',
                          cnstrSub',
                          cnstr',
                          gclause,
                          residuals ) );
                    ()
                  end
                end
                else raise (Error "Left-over normal substitutions!")
                end
            end
        | Node (nsub, children), (nsub_left, cnstrSub) ->
            begin match
              assignableLazy
                (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr)
            with
            | None -> ()
            | Some (nsub_query', (nsub_left', cnstrSub'), cnstr') ->
                S.forall children (function n, child ->
                    retrieve
                      ( child,
                        nsub_query',
                        S.copy assignSub,
                        (S.copy nsub_left', S.copy cnstrSub'),
                        cnstr' ))
            end
      in
      retrieve (child, nsub_query, assignSub, (nid (), cnstrSubId ()), cnstr)

    let retrieveCandidates (n, (Node (s, children) as sTree), gquery, r, sc) =
      let nsub_query, assignSub = (querySubId (), assignSubId ()) in
      let candSet = S.new_ () in
      let rec solveCandidate (i, candSet) =
        begin match S.lookup candSet i with
        | None -> ()
        | Some (assignSub, nsub_left, cnstrSub, cnstr, gclause, residuals) ->
          begin
            CsManager.trail (function () ->
                begin
                  S.forall nsub_left (function nv, (l, u) ->
                      begin match S.lookup cnstrSub nv with
                      | None -> raise (Error "Left-over nsubstitution")
                      | Some (I.AVar a) -> a := Some u
                      end);
                  solveResiduals
                    (gquery, gclause, residuals, assignSub, cnstr, sc)
                end);
            solveCandidate (i + 1, candSet)
          end
        end
      in
      S.insert nsub_query (1, (I.Null, (Body, r)));
      begin
        S.forall children (function _, c ->
            retrieveAll (n, c, nsub_query, assignSub, [], candSet));
        solveCandidate (1, candSet)
      end

    let matchSig a g ((I.Root (ha, s_), s) as ps) sc =
      let n, tree = Array.sub (indexArray, a) in
      retrieveCandidates (n, !tree, g, I.EClo (fst ps, snd ps), sc)

    let matchSigIt a g ((I.Root (ha, s_), s) as ps) sc =
      let n, tree = Array.sub (indexArray, a) in
      retrieval (n, !tree, g, I.EClo (fst ps, snd ps), sc)

    let sProgReset () =
      begin
        nctr := 1;
        Array.modify
          (function
            | n, tree -> begin
                n := 0;
                begin
                  tree := !(makeTree ());
                  (n, tree)
                end
              end)
          indexArray
      end

    let sProgInstall (a, C.Head (e, g, eqs, cid), r) =
      let n, tree = Array.sub (indexArray, a) in
      let nsub_goal = S.new_ () in
      S.insert nsub_goal (1, (Body, e));
      begin
        tree := insert (!tree, nsub_goal, (g, CGoals (eqs, cid, r, !n + 1)));
        n := !n + 1
      end
  end

  (* Auxiliary functions *)
  (*
     Linear normal higher-order patterns
           p ::= n | Root(c, S) | Root(b, S) | Lam (D, p)

                 where n is a linear bound ""normalized"" variable

          SP ::= p ; S | NIL

     Context
        G : context for bound variables (bvars)
            (type information is stored in the context)
        G ::= . | G, x : A

        S : context for linear normalized bound variables (nvars)
            (no type information is stored in the context)
            (these are the types of the variables definitions)
        S ::= . | S, n

     Templates: G ; S |- p
     Substitutions: G ; S |- nsub : S'

    Let s is a substitution for normalized bound variables (nvars)
    and nsub1 o nsub2 o .... o nsubn = s, s.t.
     G, S_2|- nsub1 : S_1
     G, S_3|- nsub2 : S_2
      ....
     G |- nsubn : S_n
      . ; G |- s : G, S_1

    A term U can be decomposed into a term p together with a sequenence of
    substitutions s1, s2, ..., sn such that s1 o s2 o .... o sn = s
    and the following holds:

    If    G |- U

    then

       G, S |- p

        G |- s : G, S

        G |- p[s]     and p[s] = U

   In addition:
   all expressions in the index are linear, i.e.
   an expression is first linearized before it is inserted into the index
   (this makes retrieving all axpressions from the index which unify with
    a given expression simpler, because we can omit the occurs check)

   *)
  (* ---------------------------------------------------------------*)
  (* nctr = |D| =  #normal variables *)
  (* most specific linear common generalization *)
  (* compatible (T, U) = (C, rho_u', rho_t') opt
    if
       U, T are both in normal form
       U and T share at least the top function symbol
   then
     C[rho_u'] = U and C[rho_t'] = T
   *)
  (* = S.existsOpt (fn U' => equalTerm (U, U')) *)
  (* find *i in rho_t and rho_u such that T/*i in rho_t and U/*i in rho_u *)
  (* NOTE: by invariant A1 =/= A2 *)
  (* by invariant A1 =/= A2 *)
  (* compatibleSub(nsub_t, nsub_e) = (sg, rho_t, rho_e) opt

   if dom(nsub_t) <= dom(nsub_e)
      codom(nsub_t) : linear hop in normal form (may contain normal vars)
      codom(nsub_e) : linear hop in normal form (does not contain normal vars)
   then
     nsub_t = [rho_t]sg
     nsub_e = [rho_e]sg

    G_e, Glocal_e |- nsub_e : Sigma
    G_t, Glocal_t |- nsub_t : Sigma'
    Sigma' <= Sigma

    Glocal_e ~ Glocal_t  (have approximately the same type)

   *)
  (* by invariant rho_t = empty, since nsub_t <= nsub_e *)
  (* by invariant d = d'
                                     therefore T and E have the same approximate type A *)
  (* mkNode (N, sg, r1, (G, RC), r2) = N'    *)
  (* Insertion *)
  (* compareChild (children, (n, child), n, n', (G, R)) = ()

   *)
  (* sg = nsub_t = nsub_e *)
  (* sg = nsub_t and nsub_e = sg o rho2 *)
  (* insert (N, nsub_e, (G, R2)) = N'

     if s is the substitution in node N
        G |- nsub_e : S and
    G, S' |- s : S
    then
     N' contains a path n_1 .... n_n s.t.
     [n_n] ...[n_1] s = nsub_e
  *)
  (* initial *)
  (* retrieval (U,s)
     retrieves all clauses which unify with (U,s)

     backtracking implemented via SML failure continuation

   *)
  (* cannot happen -bp *)
  (* assign (G, Us1, U2, nsub_goal, asub, csub, cnstr) = cnstr
   if G = local assumptions, G' context of query
      G1 |- U1 : V1
     G', G  |- s1 : G1
     G', G  |- U1[s1]     and s1 is an explicit substitution

      G2 |- U2 : V2
  G', G  |- asub' : G2 and asub is a assignable substitution

      U2 is eta-expanded
   then
   G2, N |- cnstr
      G2 |- csub : N
      G2 |- cnstr[csub]

      G  |- nsub_goal : N
     *)
  (* we require unique string representation of external constants *)
  (* L1 = L2 by invariant *)
  (* BVar(k2) stands for an existential variable *)
  (* S2 is an etaSpine by invariant *)
  (* BVar(k2) stands for an existential variable *)
  (* then by invariant, it must have been already instantiated *)
  (* here spine associated with k2 might not be Nil ? *)
  (* BVar(k2) stands for an existential variable *)
  (* I.Root (BVar k2, S) will be fully applied (invariant from compilation) *)
  (* Glocal_u1 |- Us1 *)
  (* by invariant Us2 cannot contain any FgnExp *)
  (* D1[s1] = D2[s2]  by invariant *)
  (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
             *)
  (* D1[s1] = D2[s2]  by invariant *)
  (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
            *)
  (* it does matter what we put in Glocal_u1! since D2 will only be approximately the same as D1 at this point! *)
  (* assignExp (nvaronly, depth+1, I.Decl (Glocal_u1, D2), (U1, I.dot1 s1), U2, cnstr) *)
  (* generate cnstr substitution for all nvars occurring in U2 *)
  (* by invariant Us2 cannot contain any FgnExp *)
  (*      | assignExpW (nvaronly, depth, Glocal_u1, (U1, s1), I.Lam (D2, U2), cnstr) =
           Cannot occur if expressions are eta expanded 
          raise Assignment ""Cannot occur if expressions in clause heads are eta-expanded""*)
  (*      | assignExpW (nvaronly, depth, Glocal_u1, (I.Lam (D1, U1), s1), U2, cnstr) =
       ETA: can't occur if eta expanded 
            raise Assignment ""Cannot occur if expressions in query are eta-expanded""
*)
  (* same reasoning holds as above *)
  (* nsub_goal, asub may be destructively updated *)
  (* assignable (g, nsub, nsub_goal, asub, csub, cnstr) = (nsub_goal', csub, cnstr') option

    nsub, nsub_goal, nsub_goal' are  well-formed normal substitutions
    asub is a well-formed assignable substitution
    csub is maps normal variables to avars

        G  |- nsub_goal
        G' |- nsub : N
        G  |- asub : G'

    G'     |- csub : N'
    G', N' |- cnstr
    G'     |- cnstr[csub]

   *)
  (* = l' *)
  (* = l *)
  (* normalize nsub_left (or require that it is normalized
             collect all left-over nsubs and later combine it with cnstrsub
           *)
  (* cnstr[rsub] *)
  (* nsub_goal1 = rgoal u nsub_goal'  remaining substitutions to be checked *)
  (* Unification *)
  (* Xs1 should not contain any uninstantiated AVar anymore *)
  (* Convert context G into explicit substitution *)
  (* ctxToEVarSub (i, G, G', asub, s) = s' *)
  (* d = I.ctxLength Glocal_u *)
  (* succeed *)
  (* B *)
  (* destructively updates assignSub, might initiate backtracking  *)
  (* cnstrSub' = empty? by invariant *)
  (* LCO optimization *)
  (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
  (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
  (* s = id *)
  (*----------------------------------------------------------------------------*)
  (* Retrieval via set of candidates *)
  (* destructively updates assignSub, might initiate backtracking  *)
  (* LCO optimization *)
  (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *)
  (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*)
  (* s = id *)
  (* print ""No candidate left anymore\n"" ;*)
  (* CGoals(AuxG, cid, ConjGoals, i) *)
  (* sc = (fn S => (O::S)) *)
  (* execute one by one all candidates : here ! *)
  (* retrieval (n, !Tree, G, I.EClo(ps), sc)   *)
  let sProgReset = sProgReset
  let sProgInstall = sProgInstall
  let matchSig = matchSigIt
end
(*!  sharing CsManager.IntSyn = IntSyn'!*)
(*! structure RBSet : RBSET !*)
(* local *)
(* functor SubTree *)

(* # 1 "src/compile/Subtree.sml.ml" *)
