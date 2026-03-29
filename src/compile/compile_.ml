(* # 1 "src/compile/compile_.sig.ml" *)
open! Basis
open CompSyn

(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(** Modified: Frank Pfenning *)
module type COMPILE = sig
  (*! structure IntSyn: INTSYN !*)
  (*! structure CompSyn: COMPSYN !*)
  exception Error of string

  type opt = CompSyn.opt

  val optimize : opt ref
  val install : IntSyn.conDecForm -> IntSyn.cid -> unit
  val sProgReset : unit -> unit
  val compileCtx : bool -> IntSyn.dec IntSyn.ctx -> CompSyn.dProg
  val compileGoal : IntSyn.dec IntSyn.ctx * IntSyn.exp -> CompSyn.goal

  (** for the meta theorem prover  --cs *)
  val compilePsi : bool -> Tomega.dec IntSyn.ctx -> CompSyn.dProg
end
(* signature COMPILE *)

(* # 1 "src/compile/compile_.fun.ml" *)
open! Basis;;
open Cprint 
(* Compilation for indexing with substitution trees *);;
(* Author: Iliano Cervesato *);;
(* Modified: Jeff Polakow, Carsten Schuermann, Larry Greenfield,
             Roberto Virga, Brigitte Pientka *);;
module MakeCompile(Compile__0: sig
                           (*! structure IntSyn' : INTSYN !*)
                           (*! structure CompSyn' : COMPSYN !*)
                           (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                           module Whnf : WHNF
                           (*! sharing Whnf.IntSyn = IntSyn' !*)
                           module TypeCheck : TYPECHECK
                           (* sharing TypeCheck.IntSyn = IntSyn' !*)
                           module SubTree : Subtree.SUBTREE
                           (*! sharing SubTree.IntSyn = IntSyn' !*)
                           (*! sharing SubTree.CompSyn = CompSyn' !*)
                           (* CPrint currently unused *)
                           module CPrint : Cprint.CPRINT
                           (*! sharing CPrint.IntSyn = IntSyn' !*)
                           (*! sharing CPrint.CompSyn = CompSyn' !*)
                           (* CPrint currently unused *)
                           module Print : PRINT
                           (*! sharing Print.IntSyn = IntSyn' !*)
                           module Names : NAMES
                           end) : COMPILE
  =
  struct
    (* FIX: need to associate errors with occurrences -kw *);;
    exception Error of string ;;
    module I = IntSyn
    module T = Tomega;;
    module C = CompSyn;;
    module SubTree = Compile__0.SubTree;;
    module Whnf = Compile__0.Whnf;;
    module CPrint = Compile__0.CPrint;;
    type duplicates = | Bvar of int 
                       | Fgn 
                       | Def of int ;;
    let rec notCS = function 
                             | fromCS_ -> false
                             | _ -> true;;
    type opt = CompSyn.opt;;
    let optimize = CompSyn.optimize;;
    let rec cidFromHead = function 
                                   | I.Const c -> c
                                   | I.Def c -> c;;
    (* isConstraint(H) = B
       where B iff H is a constant with constraint status
    *);;
    let rec isConstraint =
      function 
               | I.Const c
                   -> begin
                      match I.constStatus c
                      with 
                           | I.Constraint _ -> true
                           | _ -> false
                      end
               | h_ -> false;;
    (* head (A) = H, the head of V

       Invariants:
       G |- A : type, A enf
       A = H @ S
    *);;
    let rec head = function 
                            | I.Root (h, _) -> h
                            | I.Pi (_, a_) -> head a_;;
    let rec seen (i, vars_) = List.exists (function 
                                                    | (d, x) -> x = i) vars_;;
    (* etaSpine (S, n) = true

   iff S is a spine n;n-1;..;1;nil

   no permutations or eta-expansion of arguments are allowed
   *);;
    (*
  fun etaSpine' (I.Nil, n) = (n=0)
    | etaSpine' (I.App(U, S), n) =
        if Whnf.etaContract U = n then etaSpine' (S, n-1)
        else false

  fun etaSpine (S, n) = etaSpine' (S, n) handle Eta => false
*);;
    let rec etaSpine =
      function 
               | (I.Nil, n) -> n = 0
               | (I.App (I.Root (I.BVar k, I.Nil), s_), n)
                   -> (k = n) && (etaSpine (s_, n - 1))
               | (I.App (a_, s_), n) -> false;;
    (* collectHead (h, K, Vars, depth) = (K', Vars', replaced)
     adds to K and Vars as in collectExp and collectSpine
   *);;
    let rec collectHead =
      function 
               | ((I.BVar k as h), s_, k_, vars_, depth) -> begin
                   if k > depth then begin
                   if etaSpine (s_, depth) then begin
                   if seen (k - depth, vars_) then
                   (((depth, (Bvar (k - depth))) :: k_), vars_, true) else
                   (k_, ((depth, k - depth) :: vars_), false) end else
                   (((depth, (Bvar (k - depth))) :: k_), vars_, true) end
                   else (k_, vars_, false) end
                   (* check if h is an eta-expanded variable *)(* h is a locally bound variable and need not be collected *)
               | (_, _, k_, vars_, depth) -> (k_, vars_, false)(* check if k is in Vars *);;
    (* collectExp (U, K, Vars, depth) = (K', Vars')
      collectSpine (S, K, Vars, depth) = (K', Vars')

      Vars' - Vars = all variables seen in U or S
      K' - K = expressions in U or S to be replaced

      U, S in NF

      for each new variable (d, k-d) for depth wrt locally bound variables
   *);;
    let rec collectSpine =
      function 
               | (I.Nil, k_, vars_, depth) -> (k_, vars_)
               | (I.App (u_, s_), k_, vars_, depth)
                   -> let (k'_, vars'_) = collectExp (u_, k_, vars_, depth)
                        in collectSpine (s_, k'_, vars'_, depth)
    and collectExp =
      function 
               | (I.Root ((I.BVar k as h), s_), k_, vars_, depth)
                   -> let (k'_, vars'_, replaced) =
                        collectHead (h, s_, k_, vars_, depth) in begin
                        if replaced then (k'_, vars'_) else
                        collectSpine (s_, k'_, vars'_, depth) end
               | ((I.Root (I.Def k, s_) as u_), k_, vars_, depth)
                   -> (((depth, (Def k)) :: k_), vars_)
               | (I.Root (h, s_), k_, vars_, depth)
                   -> collectSpine (s_, k_, vars_, depth)
               | (I.Lam (d_, u_), k_, vars_, depth)
                   -> collectExp (u_, k_, vars_, depth + 1)
               | (I.FgnExp (cs, fe), k_, vars_, depth)
                   -> (((depth, Fgn) :: k_), vars_)(* don't collect D, since it is ignored in unification *)(* | collectExp (I.Uni(L), K, Vars, depth) = (K, Vars) *)(* should be impossible, Mon Apr 15 14:55:15 2002 -fp *)(* h is either const or skonst of def*);;
    (* no EVars, since U in NF *);;
    (* shiftHead (H, depth, total) = H'
     shiftExp (U, depth, total) = U'
     shiftSpine (S, depth, total) = S'

     where each variable k > depth is shifted by +total

     Invariants: U is NF, S is in NF
  *);;
    let rec shiftHead =
      function 
               | ((I.BVar k as h), depth, total) -> begin
                   if k > depth then (I.BVar (k + total)) else (I.BVar k) end
               | ((I.Const k as h), depth, total) -> h
               | ((I.Def k as h), depth, total) -> h
               | ((I.NSDef k as h), depth, total) -> h
               | ((I.FgnConst _ as h), depth, total) -> h
               | ((I.Skonst k as h), depth, total) -> h;;
    let rec shiftExp =
      function 
               | (I.Root (h, s_), depth, total)
                   -> (I.Root
                       (shiftHead (h, depth, total),
                        shiftSpine (s_, depth, total)))
               | (I.Uni l_, _, _) -> (I.Uni l_)
               | (I.Lam (d_, u_), depth, total)
                   -> (I.Lam
                       (shiftDec (d_, depth, total),
                        shiftExp (u_, depth + 1, total)))
               | (I.Pi ((d_, p_), u_), depth, total)
                   -> (I.Pi
                       ((shiftDec (d_, depth, total), p_),
                        shiftExp (u_, depth + 1, total)))
               | (I.FgnExp (csfe1, csfe2), depth, total)
                   -> I.FgnExpStd.Map.apply
                      (csfe1, csfe2)
                      (function 
                                | u_
                                    -> shiftExp
                                       (Whnf.normalize (u_, I.id), depth,
                                        total))(* Tue Apr  2 12:10:24 2002 -fp -bp *)(* this is overkill and could be very expensive for deeply nested foreign exps *)(* calling normalize here because U may not be normal *)
    and shiftSpine =
      function 
               | (I.Nil, _, _) -> I.Nil
               | (I.App (u_, s_), depth, total)
                   -> (I.App
                       (shiftExp (u_, depth, total),
                        shiftSpine (s_, depth, total)))
    and shiftDec (I.Dec (x, v_), depth, total) =
      (I.Dec (x, shiftExp (v_, depth, total)));;
    (* linearHead (Gl, h, S, left, Vars, depth, total, eqns) = (left', Vars', N, Eqn)

   if G0, Gl |- h @ S and
      h is a duplicate (i.e. it is either not fully applied pattern
       or it has already occured and is an element of Vars)

      |Gl| = depth, Gl is local context of BVars
   then
      h' is a new variable standing for a new AVar
      M = Root(h, S) where each variable in G0 is shifted by total
      N = Root(h', I.Nil)

   and
      Eqn accumulates residual equation UnifyEq(Gl, M, N)
  *);;
    let rec linearHead =
      function 
               | (g_, (I.BVar k as h), s_, left, vars_, depth, total)
                   -> begin
                   if k > depth then begin
                   if etaSpine (s_, depth) then begin
                   if seen (k - depth, vars_) then
                   (left - 1, vars_, (I.BVar (left + depth)), true) else
                   (left, ((depth, k - depth) :: vars_),
                    (I.BVar (k + total)), false)
                   end else (left - 1, vars_, (I.BVar (left + depth)), true)
                   end else (left, vars_, h, false) end
               | (g_, (I.Const k as h), s_, left, vars_, depth, total)
                   -> (left, vars_, h, false)
               | (g_, (I.FgnConst (k, conDec_) as h), s_, left, vars_, depth,
                  total) -> (left, vars_, h, false)
               | (g_, (I.Skonst k as h), s_, left, vars_, depth, total)
                   -> (left, vars_, h, false)(*
     | linearHead(G, (h as I.NSDef k), s, S, left, Vars, depth, total) =
         (left, Vars, h, false)
     *);;
    (* Def cannot occur *);;
    (* linearExp (Gl, U, left, Vars, depth, total, eqns) = (left', Vars', N, Eqn)

     call linearHead on every embedded root

     left' = left - #replaced expressions in U
     Vars' = all BVars in G0 seen in U
     N = copy of U with replaced expressions
     Eqn = residual equations

     ""For any U', U = U' iff (N = U' and Eqn)""
  *);;
    let rec linearExp =
      function 
               | (gl_, (I.Root ((I.Def k as h), s_) as u_), left, vars_,
                  depth, total, eqns)
                   -> let n_ = (I.Root ((I.BVar (left + depth)), I.Nil))
                        in let u'_ = shiftExp (u_, depth, total)
                             in (left - 1, vars_, n_,
                                 (C.UnifyEq (gl_, u'_, n_, eqns)))
               | (gl_, (I.Root (h, s_) as u_), left, vars_, depth, total,
                  eqns)
                   -> let (left', vars'_, h', replaced) =
                        linearHead (gl_, h, s_, left, vars_, depth, total)
                        in begin
                        if replaced then
                        let n_ = (I.Root (h', I.Nil))
                          in let u'_ = shiftExp (u_, depth, total)
                               in (left', vars_, n_,
                                   (C.UnifyEq (gl_, u'_, n_, eqns)))
                        else
                        let (left'', vars''_, s'_, eqns') =
                          linearSpine
                          (gl_, s_, left', vars'_, depth, total, eqns)
                          in (left'', vars''_, (I.Root (h', s'_)), eqns')
                        end (* h = h' not replaced *)
               | (gl_, I.Lam (d_, u_), left, vars_, depth, total, eqns)
                   -> let d'_ = shiftDec (d_, depth, total)
                        in let (left', vars'_, u'_, eqns') =
                             linearExp
                             ((I.Decl (gl_, d'_)), u_, left, vars_,
                              depth + 1, total, eqns)
                             in (left', vars'_, (I.Lam (d'_, u'_)), eqns')
               | (gl_, (I.FgnExp (cs, ops) as u_), left, vars_, depth, total,
                  eqns)
                   -> let n_ = (I.Root ((I.BVar (left + depth)), I.Nil))
                        in let u'_ = shiftExp (u_, depth, total)
                             in (left - 1, vars_, n_,
                                 (C.UnifyEq (gl_, u'_, n_, eqns)))(*
     | linearExp (Gl, U as I.Uni(L), left, Vars, depth, total, eqns) =
         (left, Vars, I.Uni(L), eqns)
     *)(* should be impossible  Mon Apr 15 14:54:42 2002 -fp *)
    and linearSpine =
      function 
               | (gl_, I.Nil, left, vars_, depth, total, eqns)
                   -> (left, vars_, I.Nil, eqns)
               | (gl_, I.App (u_, s_), left, vars_, depth, total, eqns)
                   -> let (left', vars'_, u'_, eqns') =
                        linearExp (gl_, u_, left, vars_, depth, total, eqns)
                        in let (left'', vars''_, s'_, eqns'') =
                             linearSpine
                             (gl_, s_, left', vars'_, depth, total, eqns')
                             in (left'', vars''_, (I.App (u'_, s'_)), eqns'');;
    (* SClo(S, s') cannot occur *);;
    (*  compileLinearHead (G, R as I.Root (h, S)) = r

       r is residual goal
       if G |- R and R might not be linear

       then

           G |- H ResGoal  and H is linear
       and of the form
           (Axists(_ , Axists( _, ....., Axists( _, Assign (E, AuxG)))))
  *);;
    let rec compileLinearHead (g_, (I.Root (h, s_) as r_)) =
      let (k_, _) = collectExp (r_, [], [], 0)
        in let left = List.length k_
             in let (left', _, r'_, eqs_) =
                  linearExp (I.Null, r_, left, [], 0, left, C.Trivial)
                  in let rec convertKRes =
                       function 
                                | (resG_, [], 0) -> resG_
                                | (resG_, ((d, k) :: k_), i)
                                    -> (C.Axists
                                        ((I.ADec
                                          ((Some ("A" ^ (Int.toString i))),
                                           d)),
                                         convertKRes (resG_, k_, i - 1)))
                       in let r =
                            convertKRes
                            ((C.Assign (r'_, eqs_)), List.rev k_, left)
                            in begin
                                 begin
                                 if (! Global.chatter) >= 6 then
                                 begin
                                   print "\nClause LH Eqn";
                                   print (CPrint.clauseToString "\t" (g_, r))
                                   end
                                 else () end;r
                                 end;;
    (*  compileSbtHead (G, R as I.Root (h, S)) = r

       r is residual goal
       if G |- R and R might not be linear

       then

           G |- H ResGoal  and H is linear

  *);;
    let rec compileSbtHead (g_, (I.Root (h, s_) as h_)) =
      let (k_, _) = collectExp (h_, [], [], 0)
        in let left = List.length k_
             in let (left', _, h'_, eqs_) =
                  linearExp (I.Null, h_, left, [], 0, left, C.Trivial)
                  in let rec convertKRes =
                       function 
                                | (g_, [], 0) -> g_
                                | (g_, ((d, k) :: k_), i)
                                    -> convertKRes
                                       ((I.Decl
                                         (g_,
                                          (I.ADec
                                           ((Some
                                             ("AVar " ^ (Int.toString i))),
                                            d)))),
                                        k_, i - 1)
                       in let g'_ = convertKRes (g_, List.rev k_, left)
                            in begin
                                 begin
                                 if (! Global.chatter) >= 6 then
                                 begin
                                   print "\nClause Sbt Eqn";
                                   print
                                   (CPrint.clauseToString
                                    "\t"
                                    (g'_, (C.Assign (h'_, eqs_))))
                                   
                                   end
                                 else () end;(g'_, (Some (h'_, eqs_)))
                                 end
                            (* insert R' together with Eqs and G and sc C.True *);;
    (* compileGoalN  fromCS A => g
     if A is a type interpreted as a subgoal in a clause and g is its
     compiled form.  No optimization is performed.

     Invariants:
     If G |- A : type,  A enf
        A has no existential type variables
     then G |- A ~> g  (A compiles to goal g)
     and  G |- g  goal

     Note: we don't accept objects that may introduce assumptions of
     constraint types, unless fromCS = true (the object come from a
     Constraint Solver module.
  *);;
    let rec compileGoalN arg__1 arg__2 =
      begin
      match (arg__1, arg__2)
      with 
           | (fromCS, (g_, (I.Root _ as r_))) -> (C.Atom r_)
           | (fromCS, (g_, I.Pi ((I.Dec (_, a1_), I.No), a2_)))
               -> let ha1_ = I.targetHead a1_
                    in let r_ = compileDClauseN fromCS false (g_, a1_)
                         in let goal =
                              compileGoalN
                              fromCS
                              ((I.Decl (g_, (I.Dec (None, a1_)))), a2_)
                              in (C.Impl (r_, a1_, ha1_, goal))
                              (* A1 is used to build the proof term, Ha1 for indexing *)(* never optimize when compiling local assumptions *)
           | (fromCS, (g_, I.Pi (((I.Dec (_, a1_) as d_), I.Maybe), a2_)))
               -> begin
               if (notCS fromCS) && (isConstraint (head a1_)) then
               raise
               ((Error "Constraint appears in dynamic clause position")) else
               (C.All (d_, compileGoalN fromCS ((I.Decl (g_, d_)), a2_))) end
      end(* A = {x:A1} A2 *)(* A = A1 -> A2 *)(* A = H @ S *)
    and compileGoal fromCS (g_, (a_, s)) =
      compileGoalN fromCS (g_, Whnf.normalize (a_, s))
    and compileDClauseN arg__3 arg__4 arg__5 =
      begin
      match (arg__3, arg__4, arg__5)
      with 
           | (fromCS, opt, (g_, (I.Root (h, s_) as r_))) -> begin
               if opt && ((! optimize) = C.LinearHeads) then  
               compileLinearHead (g_, r_) else begin
               if (notCS fromCS) && (isConstraint h) then
               raise
               ((Error "Constraint appears in dynamic clause position")) else
               (C.Eq r_) end end 
           | (fromCS, opt, (g_, I.Pi (((I.Dec (_, a1_) as d_), I.No), a2_)))
               -> (C.And
                   (compileDClauseN fromCS opt ((I.Decl (g_, d_)), a2_), a1_,
                    compileGoalN fromCS (g_, a1_)))
           | (fromCS, opt, (g_, I.Pi ((d_, I.Maybe), a2_)))
               -> (C.Exists
                   (d_, compileDClauseN fromCS opt ((I.Decl (g_, d_)), a2_)))
           | (fromCS, opt, (g_, I.Pi (((I.Dec (_, a1_) as d_), I.Meta), a2_)))
               -> (C.In
                   (compileDClauseN fromCS opt ((I.Decl (g_, d_)), a2_), a1_,
                    compileGoalN fromCS (g_, a1_)))
      end(* A = {x:A1} A2 *)(* A = {x: A1} A2, x  meta variable occuring in A2 *)(* A = A1 -> A2 *);;
    (*  compileGoalN _ should not arise by invariants *);;
    (* compileDClause A => G (top level)
     if A is a type interpreted as a clause and G is its compiled form.

     Some optimization is attempted if so flagged.

     Invariants:
     If G |- A : type, A enf
        A has no existential type variables
     then G |- A ~> r  (A compiles to residual goal r)
     and  G |- r  resgoal
  *);;
    (*  compileDClauseN _ should not arise by invariants *);;
    (* Compilation of (static) program clauses *);;
    (* compileSubgoals G' (n, Stack, G) = Subgoals  (top level)

     Invariants:
     If G : Stack
        G' ctx where G' = G, GAVar
     then Stack ~> subgoals  (Stack compiles to subgoals)
     and  G' |- subgoals
  *);;
    let rec compileSubgoals arg__6 arg__7 arg__8 =
      begin
      match (arg__6, arg__7, arg__8)
      with 
           | (fromCS, g'_,
              (n, I.Decl (stack_, I.No), I.Decl (g_, I.Dec (_, a_))))
               -> let sg = compileSubgoals fromCS g'_ (n + 1, stack_, g_)
                    in (C.Conjunct
                        (compileGoal fromCS (g'_, (a_, (I.Shift (n + 1)))),
                         (I.EClo (a_, (I.Shift (n + 1)))), sg))
                    (* G |- A and G' |- A[^(n+1)] *)
           | (fromCS, g'_,
              (n, I.Decl (stack_, I.Maybe), I.Decl (g_, I.Dec (_, a1_))))
               -> compileSubgoals fromCS g'_ (n + 1, stack_, g_)
           | (fromCS, g'_, (n, I.Null, I.Null)) -> C.True
      end;;
    (* compileSClause (Stack, G, A) => (Head, SubGoals) (top-level)
     if A is a type interpreted as a clause and (Head, SubGoals)
     is its compiled form.

     Invariants:
     If G |- A : type, A enf
        A has no existential type variables
     then G |- A ~> (Head, subgoals) ((A compiles to head and subgoals)
          where GAVar, G |- Head and GAVar, G |- subgoals
          and Head is linear and G' = GAVar, G
  *);;
    let rec compileSClauseN arg__9 arg__10 =
      begin
      match (arg__9, arg__10)
      with 
           | (fromCS, (stack_, g_, (I.Root (h, s_) as r_)))
               -> let (g'_, head_) = compileSbtHead (g_, r_)
                    in let d = (I.ctxLength g'_) - (I.ctxLength g_)
                         in let sgoals_ =
                              compileSubgoals fromCS g'_ (d, stack_, g_)
                              in ((g'_, head_), sgoals_)
                              (* G' |- Sgoals  and G' |- ^d : G *)
           | (fromCS,
              (stack_, g_, I.Pi (((I.Dec (_, a1_) as d_), I.No), a2_)))
               -> compileSClauseN
                  fromCS
                  ((I.Decl (stack_, I.No)), (I.Decl (g_, d_)), a2_)
           | (fromCS,
              (stack_, g_, I.Pi (((I.Dec (_, a1_) as d_), meta_), a2_)))
               -> compileSClauseN
                  fromCS
                  ((I.Decl (stack_, I.Meta)), (I.Decl (g_, d_)), a2_)
           | (fromCS,
              (stack_, g_, I.Pi (((I.Dec (_, a1_) as d_), I.Maybe), a2_)))
               -> compileSClauseN
                  fromCS
                  ((I.Decl (stack_, I.Maybe)), (I.Decl (g_, d_)), a2_)
      end;;
    let rec compileDClause opt (g_, a_) =
      compileDClauseN I.Ordinary opt (g_, Whnf.normalize (a_, I.id));;
    let rec compileGoal (g_, a_) =
      compileGoalN I.Ordinary (g_, Whnf.normalize (a_, I.id));;
    (* compileCtx G = (G, dPool)

     Invariants:
     If |- G ctx,
     then |- G ~> dPool  (context G compile to clause pool dPool)
     and  |- dPool  dpool
  *);;
    let rec compileCtx opt g_ =
      let rec compileBlock =
        function 
                 | ([], s, (n, i)) -> []
                 | ((I.Dec (_, v_) :: vs_), t, (n, i))
                     -> let vt_ = (I.EClo (v_, t))
                          in ((compileDClause opt (g_, vt_), I.id,
                               I.targetHead vt_)
                              :: compileBlock
                                 (vs_,
                                  (I.Dot
                                   ((I.Exp
                                     ((I.Root
                                       ((I.Proj ((I.Bidx n), i)), I.Nil)))),
                                    t)),
                                  (n, i + 1)))
        in let rec compileCtx' =
            let open CompSyn in 
             function 
                      | I.Null -> I.Null
                      | I.Decl (g_, I.Dec (_, a_))
                          -> let ha_ = I.targetHead a_
                               in (I.Decl
                                   (compileCtx' g_,
                                    (CompSyn.Dec
                                     (compileDClause opt (g_, a_), I.id, ha_))))
                      | I.Decl (g_, I.BDec (_, (c, s)))
                          -> let (g_, l_) = I.constBlock c
                               in let dpool = compileCtx' g_
                                    in let n = I.ctxLength dpool
                                         in (I.Decl
                                             (dpool,
                                              (CompSyn.BDec
                                               (compileBlock (l_, s, (n, 1))))))
                                         (* this is inefficient! -cs *)
             in (C.DProg (g_, compileCtx' g_));;
    (* compile G = (G, dPool)

     Invariants:
     If |- G ctx,
     then |- G ~> dPool  (context G compile to clause pool dPool)
     and  |- dPool  dpool
  *);;
    let rec compilePsi opt psi_ =
      let rec compileBlock =
        function 
                 | ([], s, (n, i)) -> []
                 | ((I.Dec (_, v_) :: vs_), t, (n, i))
                     -> let vt_ = (I.EClo (v_, t))
                          in ((compileDClause opt (T.coerceCtx psi_, vt_),
                               I.id, I.targetHead vt_)
                              :: compileBlock
                                 (vs_,
                                  (I.Dot
                                   ((I.Exp
                                     ((I.Root
                                       ((I.Proj ((I.Bidx n), i)), I.Nil)))),
                                    t)),
                                  (n, i + 1)))
        in let rec compileCtx' =
             function 
                      | I.Null -> I.Null
                      | I.Decl (g_, I.Dec (_, a_))
                          -> let ha_ = I.targetHead a_
                               in (I.Decl
                                   (compileCtx' g_,
                                    (CompSyn.Dec
                                     (compileDClause opt (g_, a_), I.id, ha_))))
                      | I.Decl (g_, I.BDec (_, (c, s)))
                          -> let (g_, l_) = I.constBlock c
                               in let dpool = compileCtx' g_
                                    in let n = I.ctxLength dpool
                                         in (I.Decl
                                             (dpool,
                                              (CompSyn.BDec
                                               (compileBlock (l_, s, (n, 1))))))
                                         (* this is inefficient! -cs *)
             in let rec compilePsi' =
                  function 
                           | I.Null -> I.Null
                           | I.Decl (psi_, T.UDec (I.Dec (_, a_)))
                               -> let ha_ = I.targetHead a_
                                    in (I.Decl
                                        (compilePsi' psi_,
                                         (CompSyn.Dec
                                          (compileDClause
                                           opt
                                           (T.coerceCtx psi_, a_), I.id, ha_))))
                           | I.Decl (psi_, T.UDec (I.BDec (_, (c, s))))
                               -> let (g_, l_) = I.constBlock c
                                    in let dpool = compileCtx' g_
                                         in let n = I.ctxLength dpool
                                              in (I.Decl
                                                  (dpool,
                                                   (CompSyn.BDec
                                                    (compileBlock
                                                     (l_, s, (n, 1))))))
                                              (* this is inefficient! -cs *)
                           | I.Decl (psi_, T.PDec _)
                               -> (I.Decl (compilePsi' psi_, CompSyn.PDec))
                  in (C.DProg (T.coerceCtx psi_, compilePsi' psi_));;
    (* installClause fromCS (a, A) = ()
     Effect: compiles and installs compiled form of A according to
             the specified compilation strategy
  *);;
    let rec installClause fromCS (a, a_) =
      begin
      match ! C.optimize
      with 
           | No
               -> C.sProgInstall
                  (a,
                   (C.SClause (compileDClauseN fromCS true (I.Null, a_))))
           | LinearHeads
               -> C.sProgInstall
                  (a,
                   (C.SClause (compileDClauseN fromCS true (I.Null, a_))))
           | Indexing
               -> let ((g_, head_), r_) =
                    compileSClauseN
                    fromCS
                    (I.Null, I.Null, Whnf.normalize (a_, I.id))
                    in let _ =
                         C.sProgInstall
                         (a,
                          (C.SClause
                           (compileDClauseN fromCS true (I.Null, a_))))
                         in begin
                            match head_
                            with 
                                 | None
                                     -> raise
                                        ((Error "Install via normal index"))
                                 | Some (h_, eqs_)
                                     -> SubTree.sProgInstall
                                        (cidFromHead (I.targetHead a_),
                                         (C.Head (h_, g_, eqs_, a)), r_)
                            end
      end;;
    (* compileConDec (a, condec) = ()
     Effect: install compiled form of condec in program table.
             No effect if condec has no operational meaning
  *);;
    (* Defined constants are currently not compiled *);;
    let rec compileConDec arg__11 arg__12 =
      begin
      match (arg__11, arg__12)
      with 
           | (fromCS, (a, I.ConDec (_, _, _, _, a_, (Type))))
               -> installClause fromCS (a, a_)
           | (fromCS, (a, I.SkoDec (_, _, _, a_, (Type))))
               -> begin
                  match ! C.optimize
                  with 
                       | No
                           -> C.sProgInstall
                              (a,
                               (C.SClause
                                (compileDClauseN fromCS true (I.Null, a_))))
                       | _
                           -> C.sProgInstall
                              (a,
                               (C.SClause
                                (compileDClauseN fromCS true (I.Null, a_))))
                  end
           | (I.Clause, (a, I.ConDef (_, _, _, _, a_, (I.Type), _)))
               -> C.sProgInstall
                  (a,
                   (C.SClause
                    (compileDClauseN
                     I.Clause
                     true
                     (I.Null, Whnf.normalize (a_, I.id)))))
           | (_, _) -> ()
      end(* we don't use substitution tree indexing for skolem constants yet -bp*);;
    let rec install fromCS cid = compileConDec fromCS (cid, I.sgnLookup cid);;
    let rec sProgReset () = begin
                              SubTree.sProgReset ();C.sProgReset ()
                              end;;
    end;;
(*! sharing Names.IntSyn = IntSyn' !*);;
(* local open ... *);;
(* functor Compile *);;
(* # 1 "src/compile/compile_.sml.ml" *)
open! Basis

(* Now in compsyn.fun *)
(*
structure CompSyn =
  CompSyn (structure Global = Global
           ! structure IntSyn' = IntSyn !
	   structure Names = Names
           structure Table = IntRedBlackTree);
*)
module CPrint = Cprint.Make_CPrint (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure CompSyn' = CompSyn !*)
  module Print = Print
  module Formatter = Formatter
  module Names = Names
end)

module SubTree = Subtree.SubTree (struct
  module IntSyn' = IntSyn
  module Whnf = Whnf
  module Unify = UnifyTrail
  module CompSyn' = CompSyn
  module Print = Print
  module CPrint = CPrint
  module Names = Names
  module Formatter = Formatter
  module Cs_manager = Cs_manager
  module Table = IntRedBlackTree
  module RBSet = RBSet
end)

module Compile = MakeCompile (struct
  (*! structure IntSyn' = IntSyn !*)
  (*! structure CompSyn' = CompSyn !*)
  module Whnf = Whnf
  module TypeCheck = TypeCheck
  module SubTree = SubTree
  module CPrint = CPrint
  module Print = Print
  module Names = Names
end)

module Assign__ = Assign.Assign (struct
  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Print = Print
end)

(* Re-export module types for downstream libraries *)
module type SUBTREE = Subtree.SUBTREE
module type CPRINT = Cprint.CPRINT
module type COMPSYN = COMPSYN
module type ASSIGN = Assign.ASSIGN
