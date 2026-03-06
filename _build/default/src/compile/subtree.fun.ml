open! Basis;;
(* Substitution Tree indexing *);;
(* Author: Brigitte Pientka *);;
module SubTree(SubTree__0: sig
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
                           module CPrint : CPRINT
                           (*!  sharing CPrint.IntSyn = IntSyn' !*)
                           (*!  sharing CPrint.CompSyn = CompSyn' !*)
                           (* unused *)
                           module Formatter : FORMATTER
                           (*!  sharing Print.Formatter = Formatter !*)
                           (* unused *)
                           module Names : NAMES
                           (*!  sharing Names.IntSyn = IntSyn' !*)
                           module CSManager : CS_MANAGER
                           end) : SUBTREE
  =
  struct
    (*!  structure IntSyn = IntSyn' !*);;
    (*!  structure CompSyn = CompSyn' !*);;
    (*!  structure RBSet = RBSet !*);;
    type nonrec nvar = int;;
    (* index for normal variables *);;
    type nonrec bvar = int;;
    (* index for bound variables *);;
    type nonrec bdepth = int;;
    (* depth of locally bound variables *);;
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

  *);;
    (* typeLabel distinguish between declarations (=type labels)
   which are subject to indexing, but only the internal nvars will
   be instantiated during asssignment and Body which are subject to
   indexing and existential variables and nvars will be instantiated
   during assignment
 *);;
    type typeLabel = | TypeLabel 
                     | Body ;;
    type nonrec normalSubsts = (typeLabel * IntSyn.exp_) RBSet.ordSet;;
    (* key = int = bvar *);;
    type assSub_ = | Assign of IntSyn.dec_ IntSyn.ctx_ * IntSyn.exp_ ;;
    type nonrec assSubsts = assSub_ RBSet.ordSet;;
    (* key = int = bvar *);;
    type nonrec querySubsts =
      (IntSyn.dec_ IntSyn.ctx_ * (typeLabel * IntSyn.exp_)) RBSet.ordSet;;
    type cnstr_ =
      | Eqn of IntSyn.dec_ IntSyn.ctx_ * IntSyn.exp_ * IntSyn.exp_ ;;
    type nonrec cnstrSubsts = IntSyn.exp_ RBSet.ordSet;;
    (* key = int = bvar *);;
    type cGoal_ =
      | CGoals of CompSyn.auxGoal_ * IntSyn.cid * CompSyn.conjunction_ * int ;;
    (* cid of clause *);;
    type genType = | Top 
                   | Regular ;;
    type tree_ =
      | Leaf of normalSubsts * IntSyn.dec_ IntSyn.ctx_ * cGoal_ 
      | Node of normalSubsts * tree_ RBSet.ordSet ;;
    type nonrec candidate =
      assSubsts *
      normalSubsts *
      cnstrSubsts *
      cnstr_ *
      IntSyn.dec_
      IntSyn.ctx_ *
      cGoal_;;
    (* Initialization of substitutions *);;
    let nid : unit -> normalSubsts = RBSet.new_;;
    let assignSubId : unit -> assSubsts = RBSet.new_;;
    let cnstrSubId : unit -> cnstrSubsts = RBSet.new_;;
    let querySubId : unit -> querySubsts = RBSet.new_;;
    (* Identity substitution *);;
    let rec isId s = RBSet.isEmpty s;;
    (* Initialize substitution tree *);;
    let rec makeTree () = ref ((Node (nid (), RBSet.new_ ())));;
    (* Test if node has any children *);;
    let rec noChildren c_ = RBSet.isEmpty c_;;
    (* Index array

   Invariant:
   For all type families  a  indexArray = [a1,...,an]
   where a1,...,an is a substitution tree consisting of all constants
   for target family ai

   *);;
    let indexArray =
      Array.tabulate (Global.maxCid, function 
                                              | i -> (ref 0, makeTree ()));;
    open!
      struct
        module I = IntSyn;;
        module C = CompSyn;;
        module S = RBSet;;
        exception Error of string ;;
        exception Assignment of string ;;
        exception Generalization of string ;;
        let rec cidFromHead = function 
                                       | I.Const c -> c
                                       | I.Def c -> c;;
        let rec dotn =
          function 
                   | (0, s) -> s
                   | (i, s) -> dotn (i - 1, I.dot1 s);;
        let rec compose' =
          function 
                   | (null_, g_) -> g_
                   | (IntSyn.Decl (g_, d_), g'_)
                       -> (IntSyn.Decl (compose' (g_, g'_), d_));;
        let rec shift =
          function 
                   | (null_, s) -> s
                   | (IntSyn.Decl (g_, d_), s) -> I.dot1 (shift (g_, s));;
        let rec raiseType =
          function 
                   | (null_, v_) -> v_
                   | (I.Decl (g_, d_), v_)
                       -> raiseType (g_, (I.Lam (d_, v_)));;
        let rec printSub =
          function 
                   | IntSyn.Shift n
                       -> print (("Shift " ^ (Int.toString n)) ^ "\n")
                   | IntSyn.Dot (IntSyn.Idx n, s)
                       -> begin
                            print (("Idx " ^ (Int.toString n)) ^ " . ");
                            printSub s
                            end
                   | IntSyn.Dot (IntSyn.Exp (IntSyn.EVar (_, _, _, _)), s)
                       -> begin
                            print "Exp (EVar _ ). ";printSub s
                            end
                   | IntSyn.Dot (IntSyn.Exp (IntSyn.AVar _), s)
                       -> begin
                            print "Exp (AVar _ ). ";printSub s
                            end
                   | IntSyn.Dot
                       (IntSyn.Exp (IntSyn.EClo (IntSyn.AVar _, _)), s)
                       -> begin
                            print "Exp (AVar _ ). ";printSub s
                            end
                   | IntSyn.Dot (IntSyn.Exp (IntSyn.EClo (_, _)), s)
                       -> begin
                            print "Exp (EClo _ ). ";printSub s
                            end
                   | IntSyn.Dot (IntSyn.Exp _, s)
                       -> begin
                            print "Exp (_ ). ";printSub s
                            end
                   | IntSyn.Dot (undef_, s)
                       -> begin
                            print "Undef . ";printSub s
                            end;;
        let nctr = ref 1;;
        let rec newNVar () =
          begin
            nctr := ((! nctr) + 1);(I.NVar (! nctr))
            end;;
        let rec eqHeads =
          function 
                   | (I.Const k, I.Const k') -> k = k'
                   | (I.BVar k, I.BVar k') -> k = k'
                   | (I.Def k, I.Def k') -> k = k'
                   | (_, _) -> false;;
        let rec compatible (label, t_, u_, rho_t, rho_u) =
          let rec genExp =
            function 
                     | (label, b, (I.NVar n as t_), (I.Root (h_, s_) as u_))
                         -> begin
                              S.insert rho_u (n, (label, u_));t_
                              end
                     | (label, b, (I.Root (h1_, s1_) as t_),
                        (I.Root (h2_, s2_) as u_)) -> begin
                         if eqHeads (h1_, h2_) then
                         (I.Root (h1_, genSpine (label, b, s1_, s2_))) else
                         begin
                         match b
                         with 
                              | Regular
                                  -> begin
                                       S.insert
                                       rho_t
                                       ((! nctr) + 1, (label, t_));
                                       begin
                                         S.insert
                                         rho_u
                                         ((! nctr) + 1, (label, u_));
                                         newNVar ()
                                         end
                                       
                                       end
                              | _
                                  -> raise
                                     ((Generalization "Should never happen!"))
                         end end
                     | (label, b, I.Lam ((I.Dec (n_, a1_) as d1_), t1_),
                        I.Lam ((I.Dec (_, a2_) as d2_), u2_))
                         -> (I.Lam
                             ((I.Dec
                               (n_, genExp (TypeLabel, Regular, a1_, a2_))),
                              genExp (label, b, t1_, u2_)))
                     | (label, b, I.Pi (((d1_, no_) as dd1_), e1_), I.Pi
                        (((d2_, no_) as dd2_), e2_))
                         -> (I.Pi
                             ((genDec (TypeLabel, Regular, d1_, d2_), I.no_),
                              genExp (label, b, e1_, e2_)))
                     | (label, b, I.Pi (((d1_, maybe_) as dd1_), e1_), I.Pi
                        (((d2_, maybe_) as dd2_), e2_))
                         -> (I.Pi
                             ((genDec (TypeLabel, Regular, d1_, d2_),
                               I.maybe_),
                              genExp (label, b, e1_, e2_)))
                     | (label, b, I.Pi (((d1_, meta_) as dd1_), e1_), I.Pi
                        (((d2_, meta_) as dd2_), e2_))
                         -> (I.Pi
                             ((genDec (TypeLabel, Regular, d1_, d2_),
                               I.meta_),
                              genExp (label, b, e1_, e2_)))
                     | (label, b, t_, u_)
                         -> raise
                            ((Generalization
                              "Cases where U= EVar or EClo should never happen!"))
          and genSpine =
            function 
                     | (label, b, nil_, nil_) -> I.nil_
                     | (label, b, I.App (t_, s1_), I.App (u_, s2_))
                         -> (I.App
                             (genExp (label, b, t_, u_),
                              genSpine (label, b, s1_, s2_)))
          and genDec (label, b, I.Dec (n_, e1_), I.Dec (n'_, e2_)) =
            (I.Dec (n_, genExp (label, b, e1_, e2_)))
            in let rec genTop =
                 function 
                          | (label, (I.Root (h1_, s1_) as t_),
                             (I.Root (h2_, s2_) as u_)) -> begin
                              if eqHeads (h1_, h2_) then
                              (I.Root
                               (h1_, genSpine (label, Regular, s1_, s2_)))
                              else
                              raise
                              ((Generalization
                                "Top-level function symbol not shared"))
                              end
                          | (label, I.Lam ((I.Dec (n_, a1_) as d1_), t1_),
                             I.Lam ((I.Dec (_, a2_) as d2_), u2_))
                              -> (I.Lam
                                  ((I.Dec
                                    (n_, genExp (label, Regular, a1_, a2_))),
                                   genTop (label, t1_, u2_)))
                          | (_, _, _)
                              -> raise
                                 ((Generalization
                                   "Top-level function symbol not shared"))
                 in try (Some (genTop (label, t_, u_)))
                    with 
                         | Generalization msg -> None;;
        let rec compatibleSub (nsub_t, nsub_e) =
          let (sg, rho_t, rho_e) = (nid (), nid (), nid ())
            in let _ =
                 S.forall
                 nsub_e
                 (function 
                           | (nv, (l', e_))
                               -> begin
                                  match S.lookup nsub_t nv
                                  with 
                                       | Some (l, t_) -> begin
                                           if l = l' then
                                           begin
                                           match compatible
                                                 (l, t_, e_, rho_t, rho_e)
                                           with 
                                                | None
                                                    -> begin
                                                         S.insert
                                                         rho_t
                                                         (nv, (l, t_));
                                                         S.insert
                                                         rho_e
                                                         (nv, (l, e_))
                                                         end
                                                | Some t'_
                                                    -> S.insert
                                                       sg
                                                       (nv, (l, t'_))
                                           end else
                                           raise
                                           ((Generalization
                                             "Labels don't agree\n"))
                                           end
                                       | None
                                           -> S.insert rho_e (nv, (l', e_))
                                  end)
                 in begin if isId sg then None else (Some (sg, rho_t, rho_e))
                 end;;
        let rec mkNode =
          function 
                   | (Node (_, children_), sg, rho1, ((g_, rc_) as gr_),
                      rho2)
                       -> let c = S.new_ ()
                            in begin
                                 S.insertList
                                 c
                                 [(1, (Node (rho1, children_)));
                                  (2, (Leaf (rho2, g_, rc_)))];
                                 (Node (sg, c))
                                 end
                   | (Leaf (_, g1_, rc1_), sg, rho1, ((g2_, rc2_) as gr_),
                      rho2)
                       -> let c = S.new_ ()
                            in begin
                                 S.insertList
                                 c
                                 [(1, (Leaf (rho1, g1_, rc1_)));
                                  (2, (Leaf (rho2, g2_, rc2_)))];
                                 (Node (sg, c))
                                 end;;
        let rec compareChild
          (children, (n, child), nsub_t, nsub_e,
           ((g_clause2_, res_clause2_) as gr_))
          =
          begin
          match compatibleSub (nsub_t, nsub_e)
          with 
               | None
                   -> S.insert
                      children
                      (n + 1, (Leaf (nsub_e, g_clause2_, res_clause2_)))
               | Some (sg, rho1, rho2) -> begin
                   if isId rho1 then begin
                   if isId rho2 then
                   S.insertShadow
                   children
                   (n, mkNode (child, sg, rho1, gr_, rho2)) else
                   S.insertShadow children (n, insert (child, rho2, gr_)) end
                   else
                   S.insertShadow
                   children
                   (n, mkNode (child, sg, rho1, gr_, rho2)) end
          end
        and insert =
          function 
                   | ((Leaf (nsub_t, g_clause1_, r1_) as n_), nsub_e,
                      ((g_clause2_, r2_) as gr_))
                       -> begin
                          match compatibleSub (nsub_t, nsub_e)
                          with 
                               | None
                                   -> raise
                                      ((Error
                                        "Leaf is not compatible substitution r"))
                               | Some (sg, rho1, rho2)
                                   -> mkNode (n_, sg, rho1, gr_, rho2)
                          end
                   | ((Node (_, children) as n_), nsub_e,
                      ((g_clause2_, rc_) as gr_)) -> begin
                       if noChildren children then
                       begin
                         S.insert
                         children
                         (1, (Leaf (nsub_e, g_clause2_, rc_)));n_
                         end
                       else
                       begin
                       match S.last children
                       with 
                            | (n, (Node (nsub_t, children') as child))
                                -> begin
                                     compareChild
                                     (children, (n, child), nsub_t, nsub_e,
                                      gr_);
                                     n_
                                     end
                            | (n, (Leaf (nsub_t, g1_, rc1_) as child))
                                -> begin
                                     compareChild
                                     (children, (n, child), nsub_t, nsub_e,
                                      gr_);
                                     n_
                                     end
                       end end;;
        let rec normalizeNExp =
          function 
                   | (I.NVar n, csub)
                       -> let a_ = I.newAVar ()
                            in begin
                                 S.insert csub (n, a_);a_
                                 end
                   | (I.Root (h_, s_), nsub)
                       -> (I.Root (h_, normalizeNSpine (s_, nsub)))
                   | (I.Lam (d_, u_), nsub)
                       -> (I.Lam
                           (normalizeNDec (d_, nsub),
                            normalizeNExp (u_, nsub)))
                   | (I.Pi ((d_, p_), u_), nsub)
                       -> (I.Pi
                           ((normalizeNDec (d_, nsub), p_),
                            normalizeNExp (u_, nsub)))
        and normalizeNSpine =
          function 
                   | (nil_, _) -> I.nil_
                   | (I.App (u_, s_), nsub)
                       -> (I.App
                           (normalizeNExp (u_, nsub),
                            normalizeNSpine (s_, nsub)))
        and normalizeNDec (I.Dec (n_, e_), nsub) =
          (I.Dec (n_, normalizeNExp (e_, nsub)));;
        let rec assign
          (nvaronly, glocal_u1_, us1_, u2_, nsub_goal, asub, csub, cnstr) =
          let depth = I.ctxLength glocal_u1_
            in let rec assignHead
                 (nvaronly, depth, glocal_u1_,
                  ((I.Root (h1_, s1_), s1) as us1_),
                  (I.Root (h2_, s2_) as u2_), cnstr)
                 =
                 begin
                 match (h1_, h2_)
                 with 
                      | (I.Const c1, I.Const c2) -> begin
                          if c1 = c2 then
                          assignSpine
                          (nvaronly, depth, glocal_u1_, (s1_, s1), s2_,
                           cnstr)
                          else raise ((Assignment "Constant clash")) end
                      | (I.Skonst c1, I.Skonst c2) -> begin
                          if c1 = c2 then
                          assignSpine
                          (nvaronly, depth, glocal_u1_, (s1_, s1), s2_,
                           cnstr)
                          else raise ((Assignment "Skolem constant clash"))
                          end
                      | (I.Def d1, _)
                          -> assignExp
                             (nvaronly, depth, glocal_u1_,
                              Whnf.expandDef us1_, u2_, cnstr)
                      | (I.FgnConst (cs1, I.ConDec (n1, _, _, _, _, _)),
                         I.FgnConst (cs2, I.ConDec (n2, _, _, _, _, _)))
                          -> begin
                          if (cs1 = cs2) && (n1 = n2) then cnstr else
                          raise ((Assignment "Foreign Constant clash")) end
                      | (I.FgnConst (cs1, I.ConDef (n1, _, _, w1_, _, _, _)),
                         I.FgnConst
                         (cs2, I.ConDef (n2, _, _, v_, w2_, _, _))) -> begin
                          if (cs1 = cs2) && (n1 = n2) then cnstr else
                          assignExp
                          (nvaronly, depth, glocal_u1_, (w1_, s1), w2_,
                           cnstr)
                          end
                      | (I.FgnConst (_, I.ConDef (_, _, _, w1_, _, _, _)), _)
                          -> assignExp
                             (nvaronly, depth, glocal_u1_, (w1_, s1), u2_,
                              cnstr)
                      | (_, I.FgnConst (_, I.ConDef (_, _, _, w2_, _, _, _)))
                          -> assignExp
                             (nvaronly, depth, glocal_u1_, us1_, w2_, cnstr)
                      | (_, _) -> raise ((Assignment "Head mismatch "))
                 end
               and assignExpW =
                 function 
                          | (nvaronly, depth, glocal_u1_, (I.Uni l1_, s1),
                             I.Uni l2_, cnstr) -> cnstr
                          | (nvaronly, depth, glocal_u1_, us1_, I.NVar n,
                             cnstr)
                              -> begin
                                   S.insert
                                   nsub_goal
                                   (n,
                                    (glocal_u1_, (nvaronly, (I.EClo us1_))));
                                   cnstr
                                   end
                          | (Body, depth, glocal_u1_,
                             ((I.Root (h1_, s1_), s1) as us1_),
                             (I.Root (h2_, s2_) as u2_), cnstr)
                              -> begin
                                 match h2_
                                 with 
                                      | I.BVar k2 -> begin
                                          if k2 > depth then
                                          begin
                                            S.insert
                                            asub
                                            (k2 - (I.ctxLength glocal_u1_),
                                             (Assign
                                              (glocal_u1_, (I.EClo us1_))));
                                            cnstr
                                            end
                                          else
                                          begin
                                          match h1_
                                          with 
                                               | I.BVar k1 -> begin
                                                   if k1 = k2 then
                                                   assignSpine
                                                   (Body, depth, glocal_u1_,
                                                    (s1_, s1), s2_, cnstr)
                                                   else
                                                   raise
                                                   ((Assignment
                                                     "Bound variable clash"))
                                                   end
                                               | _
                                                   -> raise
                                                      ((Assignment
                                                        "Head mismatch"))
                                          end end
                                      | _
                                          -> assignHead
                                             (Body, depth, glocal_u1_, us1_,
                                              u2_, cnstr)
                                 end
                          | (TypeLabel, depth, glocal_u1_,
                             ((I.Root (h1_, s1_), s1) as us1_),
                             (I.Root (h2_, s2_) as u2_), cnstr)
                              -> begin
                                 match h2_
                                 with 
                                      | I.BVar k2 -> begin
                                          if k2 > depth then cnstr else
                                          begin
                                          match h1_
                                          with 
                                               | I.BVar k1 -> begin
                                                   if k1 = k2 then
                                                   assignSpine
                                                   (TypeLabel, depth,
                                                    glocal_u1_, (s1_, s1),
                                                    s2_, cnstr)
                                                   else
                                                   raise
                                                   ((Assignment
                                                     "Bound variable clash"))
                                                   end
                                               | _
                                                   -> raise
                                                      ((Assignment
                                                        "Head mismatch"))
                                          end end
                                      | _
                                          -> assignHead
                                             (TypeLabel, depth, glocal_u1_,
                                              us1_, u2_, cnstr)
                                 end
                          | (nvaronly, depth, glocal_u1_, us1_,
                             (I.Root (I.BVar k2, s_) as u2_), cnstr) -> begin
                              if k2 > depth then
                              begin
                              match nvaronly
                              with 
                                   | TypeLabel -> cnstr
                                   | Body
                                       -> begin
                                            S.insert
                                            asub
                                            (k2 - depth,
                                             (Assign
                                              (glocal_u1_, (I.EClo us1_))));
                                            cnstr
                                            end
                              end else
                              begin
                              match nvaronly
                              with 
                                   | TypeLabel -> cnstr
                                   | Body
                                       -> begin
                                          match us1_
                                          with 
                                               | (I.EVar (r, _, v_, cnstr_),
                                                  s)
                                                   -> let u2'_ =
                                                        normalizeNExp
                                                        (u2_, csub)
                                                        in ((Eqn
                                                             (glocal_u1_,
                                                              (I.EClo us1_),
                                                              u2'_))
                                                            :: cnstr)
                                               | (I.EClo (u_, s'), s)
                                                   -> assignExp
                                                      (Body, depth,
                                                       glocal_u1_,
                                                       (u_, I.comp (s', s)),
                                                       u2_, cnstr)
                                               | (I.FgnExp (_, ops), _)
                                                   -> let u2'_ =
                                                        normalizeNExp
                                                        (u2_, csub)
                                                        in ((Eqn
                                                             (glocal_u1_,
                                                              (I.EClo us1_),
                                                              u2'_))
                                                            :: cnstr)
                                          end
                              end end
                          | (nvaronly, depth, glocal_u1_,
                             (I.Lam ((I.Dec (_, a1_) as d1_), u1_), s1),
                             I.Lam ((I.Dec (_, a2_) as d2_), u2_), cnstr)
                              -> let cnstr' =
                                   assignExp
                                   (TypeLabel, depth, glocal_u1_, (a1_, s1),
                                    a2_, cnstr)
                                   in assignExp
                                      (nvaronly, depth + 1,
                                       (I.Decl
                                        (glocal_u1_, I.decSub (d1_, s1))),
                                       (u1_, I.dot1 s1), u2_, cnstr')
                          | (nvaronly, depth, glocal_u1_,
                             (I.Pi (((I.Dec (_, a1_) as d1_), _), u1_), s1),
                             I.Pi (((I.Dec (_, a2_) as d2_), _), u2_), cnstr)
                              -> let cnstr' =
                                   assignExp
                                   (TypeLabel, depth, glocal_u1_, (a1_, s1),
                                    a2_, cnstr)
                                   in assignExp
                                      (nvaronly, depth + 1,
                                       (I.Decl
                                        (glocal_u1_, I.decSub (d1_, s1))),
                                       (u1_, I.dot1 s1), u2_, cnstr')
                          | (nvaronly, depth, glocal_u1_,
                             ((I.EVar (r, _, v_, cnstr_), s) as us1_), u2_,
                             cnstr)
                              -> let u2'_ = normalizeNExp (u2_, csub)
                                   in ((Eqn
                                        (glocal_u1_, (I.EClo us1_), u2'_))
                                       :: cnstr)
                          | (nvaronly, depth, glocal_u1_,
                             ((I.EClo (u_, s'), s) as us1_), u2_, cnstr)
                              -> assignExp
                                 (nvaronly, depth, glocal_u1_,
                                  (u_, I.comp (s', s)), u2_, cnstr)
                          | (nvaronly, depth, glocal_u1_,
                             ((I.FgnExp (_, ops), _) as us1_), u2_, cnstr)
                              -> let u2'_ = normalizeNExp (u2_, csub)
                                   in ((Eqn
                                        (glocal_u1_, (I.EClo us1_), u2'_))
                                       :: cnstr)
                          | (nvaronly, depth, glocal_u1_, us1_,
                             (I.FgnExp (_, ops) as u2_), cnstr)
                              -> ((Eqn (glocal_u1_, (I.EClo us1_), u2_))
                                  :: cnstr)
               and assignSpine =
                 function 
                          | (nvaronly, depth, glocal_u1_, (nil_, _), nil_,
                             cnstr) -> cnstr
                          | (nvaronly, depth, glocal_u1_,
                             (I.SClo (s1_, s1'), s1), s_, cnstr)
                              -> assignSpine
                                 (nvaronly, depth, glocal_u1_,
                                  (s1_, I.comp (s1', s1)), s_, cnstr)
                          | (nvaronly, depth, glocal_u1_,
                             (I.App (u1_, s1_), s1), I.App (u2_, s2_), cnstr)
                              -> let cnstr' =
                                   assignExp
                                   (nvaronly, depth, glocal_u1_, (u1_, s1),
                                    u2_, cnstr)
                                   in assignSpine
                                      (nvaronly, depth, glocal_u1_,
                                       (s1_, s1), s2_, cnstr')
               and assignExp (nvaronly, depth, glocal_u1_, us1_, u2_, cnstr)
                 =
                 assignExpW
                 (nvaronly, depth, glocal_u1_, Whnf.whnf us1_, u2_, cnstr)
                 in assignExp (nvaronly, depth, glocal_u1_, us1_, u2_, cnstr);;
        let rec assignableLazy
          (nsub, nsub_query, assignSub, (nsub_left, cnstrSub), cnstr) =
          let nsub_query' = querySubId ()
            in let cref = ref cnstr
                 in let rec assign' (nsub_query, nsub) =
                      let (nsub_query_left, nsub_left1) =
                        S.differenceModulo
                        nsub_query
                        nsub
                        (function 
                                  | (glocal_u_, (l, u_))
                                      -> function 
                                                  | (l', t_)
                                                      -> cref :=
                                                           (assign
                                                            (l, glocal_u_,
                                                             (u_, I.id), t_,
                                                             nsub_query',
                                                             assignSub,
                                                             cnstrSub,
                                                             ! cref)))
                        in let nsub_left' =
                             S.update
                             nsub_left1
                             (function 
                                       | (l, u_)
                                           -> (l,
                                               normalizeNExp (u_, cnstrSub)))
                             in (Some
                                 (S.union nsub_query_left nsub_query',
                                  (S.union nsub_left nsub_left', cnstrSub),
                                  ! cref))
                      in try assign' (nsub_query, nsub)
                         with 
                              | Assignment msg -> None;;
        let rec assignableEager
          (nsub, nsub_query, assignSub, cnstrSub, cnstr) =
          let nsub_query' = querySubId ()
            in let cref = ref cnstr
                 in let rec assign' (nsub_query, nsub) =
                      let (nsub_query_left, nsub_left) =
                        S.differenceModulo
                        nsub_query
                        nsub
                        (function 
                                  | (glocal_u_, (l, u_))
                                      -> function 
                                                  | (l', t_)
                                                      -> cref :=
                                                           (assign
                                                            (l', glocal_u_,
                                                             (u_, I.id), t_,
                                                             nsub_query',
                                                             assignSub,
                                                             cnstrSub,
                                                             ! cref)))
                        in let _ =
                             S.forall
                             nsub_left
                             (function 
                                       | (nv, (nvaronly, u_))
                                           -> begin
                                              match S.lookup cnstrSub nv
                                              with 
                                                   | None
                                                       -> raise
                                                          ((Error
                                                            "Left-over nsubstitution"))
                                                   | Some (I.AVar a_)
                                                       -> a_ :=
                                                            ((Some
                                                              (normalizeNExp
                                                               (u_, cnstrSub))))
                                              end)
                             in (Some
                                 (S.union nsub_query_left nsub_query',
                                  cnstrSub, ! cref))
                      in try assign' (nsub_query, nsub)
                         with 
                              | Assignment msg -> None;;
        let rec unifyW =
          function 
                   | (g_,
                      ((I.AVar (({ contents = None} as r)) as x_), I.Shift 0),
                      us2_) -> r := ((Some ((I.EClo us2_))))
                   | (g_, ((I.AVar (({ contents = None} as r)) as x_), s),
                      ((u_, s2) as us2_))
                       -> begin
                            print "unifyW -- not s = Id\n";
                            begin
                              print
                              (("Us2 = " ^
                                  (Print.expToString (g_, (I.EClo us2_))))
                                 ^ "\n");
                              r := ((Some ((I.EClo us2_))))
                              end
                            
                            end
                   | (g_, xs1_, us2_) -> Unify.unifyW (g_, xs1_, us2_);;
        let rec unify (g_, xs1_, us2_) =
          unifyW (g_, Whnf.whnf xs1_, Whnf.whnf us2_);;
        let rec unifiable (g_, us1_, us2_) =
          try begin
                unify (g_, us1_, us2_);true
                end
          with 
               | Unify.Unify msg -> false;;
        let rec ctxToExplicitSub =
          function 
                   | (i, gquery_, null_, asub) -> I.id
                   | (i, gquery_, I.Decl (gclause_, I.Dec (_, a_)), asub)
                       -> let s =
                            ctxToExplicitSub (i + 1, gquery_, gclause_, asub)
                            in let (I.EVar (x'_, _, _, _) as u'_) =
                                 I.newEVar (gquery_, (I.EClo (a_, s)))
                                 in begin
                                      begin
                                      match S.lookup asub i
                                      with 
                                           | None -> ()
                                           | Some (Assign (glocal_u_, u_))
                                               -> x'_ :=
                                                    ((Some
                                                      (raiseType
                                                       (glocal_u_, u_))))
                                      end;(I.Dot ((I.Exp u'_), s))
                                      end
                   | (i, gquery_, I.Decl (gclause_, I.ADec (_, d)), asub)
                       -> let (I.AVar x'_ as u'_) = I.newAVar ()
                            in begin
                                 begin
                                 match S.lookup asub i
                                 with 
                                      | None -> ()
                                      | Some (Assign (glocal_u_, u_))
                                          -> x'_ := ((Some u_))
                                 end;
                                 (I.Dot
                                  ((I.Exp ((I.EClo (u'_, (I.Shift (- d)))))),
                                   ctxToExplicitSub
                                   (i + 1, gquery_, gclause_, asub)))
                                 
                                 end;;
        let rec solveAuxG =
          function 
                   | (trivial_, s, gquery_) -> true
                   | (C.UnifyEq (glocal_, e1, n_, eqns), s, gquery_)
                       -> let g_ = compose' (glocal_, gquery_)
                            in let s' = shift (glocal_, s) in begin
                                 if unifiable (g_, (n_, s'), (e1, s')) then
                                 solveAuxG (eqns, s, gquery_) else false end;;
        let rec solveCnstr =
          function 
                   | (gquery_, gclause_, [], s) -> true
                   | (gquery_, gclause_, (Eqn (glocal_, u1_, u2_) :: cnstr_),
                      s)
                       -> (Unify.unifiable
                           (compose' (gquery_, glocal_), (u1_, I.id),
                            (u2_, shift (glocal_, s)))) &&
                            (solveCnstr (gquery_, gclause_, cnstr_, s));;
        let rec solveResiduals
          (gquery_, gclause_, CGoals (auxG_, cid, conjGoals_, i), asub,
           cnstr', sc)
          =
          let s = ctxToExplicitSub (1, gquery_, gclause_, asub)
            in let success =
                 (solveAuxG (auxG_, s, gquery_)) &&
                   (solveCnstr (gquery_, gclause_, cnstr', s))
                 in begin if success then sc ((conjGoals_, s), cid) else ()
                 end;;
        let rec ithChild (CGoals (_, _, _, i), n) = i = n;;
        let rec retrieveChild
          (num, child_, nsub_query, assignSub, cnstr, gquery_, sc) =
          let rec retrieve =
            function 
                     | (Leaf (nsub, gclause_, residuals_), nsub_query,
                        assignSub, cnstrSub, cnstr)
                         -> begin
                            match assignableEager
                                  (nsub, nsub_query, assignSub, cnstrSub,
                                   cnstr)
                            with 
                                 | None -> ()
                                 | Some (nsub_query', cnstrSub', cnstr')
                                     -> begin
                                     if isId nsub_query' then begin
                                     if ithChild (residuals_, ! num) then
                                     solveResiduals
                                     (gquery_, gclause_, residuals_,
                                      assignSub, cnstr', sc)
                                     else
                                     CSManager.trail
                                     (function 
                                               | ()
                                                   -> solveResiduals
                                                      (gquery_, gclause_,
                                                       residuals_, assignSub,
                                                       cnstr', sc))
                                     end else
                                     raise
                                     ((Error
                                       "Left-over normal substitutions!"))
                                     end
                            end
                     | (Node (nsub, children_), nsub_query, assignSub,
                        cnstrSub, cnstr)
                         -> begin
                            match assignableEager
                                  (nsub, nsub_query, assignSub, cnstrSub,
                                   cnstr)
                            with 
                                 | None -> ()
                                 | Some (nsub_query', cnstrSub', cnstr')
                                     -> S.forall
                                        children_
                                        (function 
                                                  | (n, child_)
                                                      -> retrieve
                                                         (child_,
                                                          nsub_query',
                                                          S.copy assignSub,
                                                          S.copy cnstrSub',
                                                          cnstr'))
                            end
            in retrieve (child_, nsub_query, assignSub, cnstrSubId (), cnstr);;
        let rec retrieval (n, (Node (s, children_) as sTree_), g_, r, sc) =
          let (nsub_query, assignSub) = (querySubId (), assignSubId ())
            in begin
                 S.insert nsub_query (1, (I.null_, (Body, r)));
                 S.forall
                 children_
                 (function 
                           | (_, c_)
                               -> retrieveChild
                                  (n, c_, nsub_query, assignSub, [], g_, sc))
                 
                 end;;
        let rec retrieveAll
          (num, child_, nsub_query, assignSub, cnstr, candSet) =
          let i = ref 0
            in let rec retrieve =
                 function 
                          | (Leaf (nsub, gclause_, residuals_), nsub_query,
                             assignSub, (nsub_left, cnstrSub), cnstr)
                              -> begin
                                 match assignableLazy
                                       (nsub, nsub_query, assignSub,
                                        (nsub_left, cnstrSub), cnstr)
                                 with 
                                      | None -> ()
                                      | Some
                                          (nsub_query',
                                           (nsub_left', cnstrSub'), cnstr')
                                          -> begin
                                          if isId nsub_query' then
                                          begin
                                            i := ((! i) + 1);
                                            begin
                                              S.insert
                                              candSet
                                              (! i,
                                               (assignSub, nsub_left',
                                                cnstrSub', cnstr', gclause_,
                                                residuals_));
                                              ()
                                              end
                                            
                                            end
                                          else
                                          raise
                                          ((Error
                                            "Left-over normal substitutions!"))
                                          end
                                 end
                          | (Node (nsub, children_), nsub_query, assignSub,
                             (nsub_left, cnstrSub), cnstr)
                              -> begin
                                 match assignableLazy
                                       (nsub, nsub_query, assignSub,
                                        (nsub_left, cnstrSub), cnstr)
                                 with 
                                      | None -> ()
                                      | Some
                                          (nsub_query',
                                           (nsub_left', cnstrSub'), cnstr')
                                          -> S.forall
                                             children_
                                             (function 
                                                       | (n, child_)
                                                           -> retrieve
                                                              (child_,
                                                               nsub_query',
                                                               S.copy
                                                               assignSub,
                                                               (S.copy
                                                                nsub_left',
                                                                S.copy
                                                                cnstrSub'),
                                                               cnstr'))
                                 end
                 in retrieve
                    (child_, nsub_query, assignSub, (nid (), cnstrSubId ()),
                     cnstr);;
        let rec retrieveCandidates
          (n, (Node (s, children_) as sTree_), gquery_, r, sc) =
          let (nsub_query, assignSub) = (querySubId (), assignSubId ())
            in let candSet = S.new_ ()
                 in let rec solveCandidate (i, candSet) =
                      begin
                      match S.lookup candSet i
                      with 
                           | None -> ()
                           | Some
                               (assignSub, nsub_left, cnstrSub, cnstr,
                                gclause_, residuals_)
                               -> begin
                                    CSManager.trail
                                    (function 
                                              | ()
                                                  -> begin
                                                       S.forall
                                                       nsub_left
                                                       (function 
                                                                 | (nv,
                                                                    (l, u_))
                                                                    -> 
                                                                    begin
                                                                    match 
                                                                    S.lookup
                                                                    cnstrSub
                                                                    nv
                                                                    with 
                                                                    
                                                                    | 
                                                                    None
                                                                    -> 
                                                                    raise
                                                                    ((Error
                                                                    "Left-over nsubstitution"))
                                                                    | 
                                                                    Some
                                                                    (I.AVar
                                                                    a_)
                                                                    -> 
                                                                    a_ :=
                                                                    ((Some
                                                                    u_))
                                                                    end);
                                                       solveResiduals
                                                       (gquery_, gclause_,
                                                        residuals_,
                                                        assignSub, cnstr, sc)
                                                       
                                                       end);
                                    solveCandidate (i + 1, candSet)
                                    end
                      end
                      in begin
                           S.insert nsub_query (1, (I.null_, (Body, r)));
                           begin
                             S.forall
                             children_
                             (function 
                                       | (_, c_)
                                           -> retrieveAll
                                              (n, c_, nsub_query, assignSub,
                                               [], candSet));
                             solveCandidate (1, candSet)
                             end
                           
                           end;;
        let rec matchSig (a, g_, ((I.Root (ha_, s_), s) as ps), sc) =
          let (n, tree_) = Array.sub (indexArray, a)
            in retrieveCandidates (n, ! tree_, g_, (I.EClo ps), sc);;
        let rec matchSigIt (a, g_, ((I.Root (ha_, s_), s) as ps), sc) =
          let (n, tree_) = Array.sub (indexArray, a)
            in retrieval (n, ! tree_, g_, (I.EClo ps), sc);;
        let rec sProgReset () =
          begin
            nctr := 1;
            Array.modify
            (function 
                      | (n, tree_)
                          -> begin
                               n := 0;
                               begin
                                 tree_ := (! (makeTree ()));(n, tree_)
                                 end
                               
                               end)
            indexArray
            end;;
        let rec sProgInstall (a, C.Head (e_, g_, eqs_, cid), r_) =
          let (n, tree_) = Array.sub (indexArray, a)
            in let nsub_goal = S.new_ ()
                 in begin
                      S.insert nsub_goal (1, (Body, e_));
                      begin
                        tree_ :=
                          (insert
                           (! tree_, nsub_goal,
                            (g_, (CGoals (eqs_, cid, r_, (! n) + 1)))));
                        n := ((! n) + 1)
                        end
                      
                      end;;
        end;;
    (* Auxiliary functions *);;
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

   *);;
    (* ---------------------------------------------------------------*);;
    (* nctr = |D| =  #normal variables *);;
    (* most specific linear common generalization *);;
    (* compatible (T, U) = (C, rho_u', rho_t') opt
    if
       U, T are both in normal form
       U and T share at least the top function symbol
   then
     C[rho_u'] = U and C[rho_t'] = T
   *);;
    (* = S.existsOpt (fn U' => equalTerm (U, U')) *);;
    (* find *i in rho_t and rho_u such that T/*i in rho_t and U/*i in rho_u *);;
    (* NOTE: by invariant A1 =/= A2 *);;
    (* by invariant A1 =/= A2 *);;
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

   *);;
    (* by invariant rho_t = empty, since nsub_t <= nsub_e *);;
    (* by invariant d = d'
                                     therefore T and E have the same approximate type A *);;
    (* mkNode (N, sg, r1, (G, RC), r2) = N'    *);;
    (* Insertion *);;
    (* compareChild (children, (n, child), n, n', (G, R)) = ()

   *);;
    (* sg = nsub_t = nsub_e *);;
    (* sg = nsub_t and nsub_e = sg o rho2 *);;
    (* insert (N, nsub_e, (G, R2)) = N'

     if s is the substitution in node N
        G |- nsub_e : S and
    G, S' |- s : S
    then
     N' contains a path n_1 .... n_n s.t.
     [n_n] ...[n_1] s = nsub_e
  *);;
    (* initial *);;
    (* retrieval (U,s)
     retrieves all clauses which unify with (U,s)

     backtracking implemented via SML failure continuation

   *);;
    (* cannot happen -bp *);;
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
     *);;
    (* we require unique string representation of external constants *);;
    (* L1 = L2 by invariant *);;
    (* BVar(k2) stands for an existential variable *);;
    (* S2 is an etaSpine by invariant *);;
    (* BVar(k2) stands for an existential variable *);;
    (* then by invariant, it must have been already instantiated *);;
    (* here spine associated with k2 might not be Nil ? *);;
    (* BVar(k2) stands for an existential variable *);;
    (* I.Root (BVar k2, S) will be fully applied (invariant from compilation) *);;
    (* Glocal_u1 |- Us1 *);;
    (* by invariant Us2 cannot contain any FgnExp *);;
    (* D1[s1] = D2[s2]  by invariant *);;
    (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
             *);;
    (* D1[s1] = D2[s2]  by invariant *);;
    (* nsub_goal may be destructively updated,
               asub does not change (i.e. existential variables are not instantiated,
               by invariant they must have been already instantiated
            *);;
    (* it does matter what we put in Glocal_u1! since D2 will only be approximately the same as D1 at this point! *);;
    (* assignExp (nvaronly, depth+1, I.Decl (Glocal_u1, D2), (U1, I.dot1 s1), U2, cnstr) *);;
    (* generate cnstr substitution for all nvars occurring in U2 *);;
    (* by invariant Us2 cannot contain any FgnExp *);;
    (*      | assignExpW (nvaronly, depth, Glocal_u1, (U1, s1), I.Lam (D2, U2), cnstr) =
           Cannot occur if expressions are eta expanded 
          raise Assignment ""Cannot occur if expressions in clause heads are eta-expanded""*);;
    (*      | assignExpW (nvaronly, depth, Glocal_u1, (I.Lam (D1, U1), s1), U2, cnstr) =
       ETA: can't occur if eta expanded 
            raise Assignment ""Cannot occur if expressions in query are eta-expanded""
*);;
    (* same reasoning holds as above *);;
    (* nsub_goal, asub may be destructively updated *);;
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

   *);;
    (* = l' *);;
    (* = l *);;
    (* normalize nsub_left (or require that it is normalized
             collect all left-over nsubs and later combine it with cnstrsub
           *);;
    (* cnstr[rsub] *);;
    (* nsub_goal1 = rgoal u nsub_goal'  remaining substitutions to be checked *);;
    (* Unification *);;
    (* Xs1 should not contain any uninstantiated AVar anymore *);;
    (* Convert context G into explicit substitution *);;
    (* ctxToEVarSub (i, G, G', asub, s) = s' *);;
    (* d = I.ctxLength Glocal_u *);;
    (* succeed *);;
    (* B *);;
    (* destructively updates assignSub, might initiate backtracking  *);;
    (* cnstrSub' = empty? by invariant *);;
    (* LCO optimization *);;
    (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *);;
    (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*);;
    (* s = id *);;
    (*----------------------------------------------------------------------------*);;
    (* Retrieval via set of candidates *);;
    (* destructively updates assignSub, might initiate backtracking  *);;
    (* LCO optimization *);;
    (* destructively updates nsub_query, assignSub,  might fail and initiate backtracking *);;
    (* we must undo any changes to assignSub and whatever else is destructively updated,
             cnstrSub?, cnstr? or keep them separate from different branches!*);;
    (* s = id *);;
    (* print ""No candidate left anymore\n"" ;*);;
    (* CGoals(AuxG, cid, ConjGoals, i) *);;
    (* sc = (fn S => (O::S)) *);;
    (* execute one by one all candidates : here ! *);;
    (* retrieval (n, !Tree, G, I.EClo(ps), sc)   *);;
    let sProgReset = sProgReset;;
    let sProgInstall = sProgInstall;;
    let matchSig = matchSigIt;;
    end;;
(*!  sharing CSManager.IntSyn = IntSyn'!*);;
(*! structure RBSet : RBSET !*);;
(* local *);;
(* functor SubTree *);;