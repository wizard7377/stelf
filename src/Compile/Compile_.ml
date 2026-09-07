open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Formatter__Formatter_
open! Typecheck.Typecheck_
open! Solvers.Solvers_

(* # 1 "src/compile/Compile_.sig.ml" *)
open CompSyn

(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)

include COMPILE
(** Modified: Frank Pfenning *)

(* signature COMPILE *)

(* # 1 "src/compile/Compile_.fun.ml" *)
open! Basis
open Cprint
(* Compilation for indexing with substitution trees *)

(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Carsten Schuermann, Larry Greenfield,
             Roberto Virga, Brigitte Pientka *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MakeCompile
    (Whnf : WHNF)
    (TypeCheck : TYPECHECK)
    (SubTree : Subtree.SUBTREE)
    (CPrint : Cprint.CPRINT)
    (Print : PRINT)
    (Names : NAMES) : COMPILE = struct
  (*
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  (*! sharing Whnf.IntSyn = IntSyn' !*)
  (* sharing TypeCheck.IntSyn = IntSyn' !*)
  (*! sharing SubTree.IntSyn = IntSyn' !*)
  (*! sharing SubTree.CompSyn = CompSyn' !*)
  (*! sharing CPrint.IntSyn = IntSyn' !*)
  (*! sharing CPrint.CompSyn = CompSyn' !*)
  (*! sharing Print.IntSyn = IntSyn' !*)
*)
  (* FIX: need to associate errors with occurrences -kw *)
  exception Error = Error

  module I = IntSyn
  module T = Tomega
  module C = CompSyn
  module SubTree = SubTree
  module Whnf = Whnf
  module CPrint = CPrint

  type duplicates = Bvar of int | Fgn | Def of int

  let notCS = function fromCS -> false | _ -> true

  type opt = CompSyn.opt

  let optimize = CompSyn.optimize
  let cidFromHead = function I.Const c -> c | I.Def c -> c

  (* isConstraint(H) = B
       where B iff H is a constant with constraint status
    *)
  let isConstraint = function
    | I.Const c ->
        begin match I.constStatus c with I.Constraint _ -> true | _ -> false
        end
    | h -> false

  (* head (A) = H, the head of V

       Invariants:
       G |- A : type, A enf
       A = H @ S
    *)
  let rec head = function I.Root (h, _) -> h | I.Pi (_, a) -> head a
  let seen (i, vars) = List.exists (function d, x -> x = i) vars

  (* etaSpine (S, n) = true

   iff S is a spine n;n-1;..;1;nil

   no permutations or eta-expansion of arguments are allowed
   *)
  (*
  fun etaSpine' (I.Nil, n) = (n=0)
    | etaSpine' (I.App(U, S), n) =
        if Whnf.etaContract U = n then etaSpine' (S, n-1)
        else false

  fun etaSpine (S, n) = etaSpine' (S, n) handle Eta => false
*)
  let rec etaSpine (a, n) = match a with
    | I.Nil -> n = 0
    | I.App (I.Root (I.BVar k, I.Nil), s) -> k = n && etaSpine (s, n - 1)
    | I.App (a, s) -> false

  (* collectHead (h, K, Vars, depth) = (K', Vars', replaced)
     adds to K and Vars as in collectExp and collectSpine
   *)
  let collectHead (a, s, k_, vars, depth) = match a with
    | (I.BVar k as h) ->
        begin if k > depth then
          begin if etaSpine (s, depth) then
            begin if seen (k - depth, vars) then
              ((depth, Bvar (k - depth)) :: k_, vars, true)
            else (k_, (depth, k - depth) :: vars, false)
            end
          else ((depth, Bvar (k - depth)) :: k_, vars, true)
          end
        else (k_, vars, false)
        end
    | _ -> (k_, vars, false)

  (* collectExp (U, K, Vars, depth) = (K', Vars')
      collectSpine (S, K, Vars, depth) = (K', Vars')

      Vars' - Vars = all variables seen in U or S
      K' - K = expressions in U or S to be replaced

      U, S in NF

      for each new variable (d, k-d) for depth wrt locally bound variables
   *)
  let rec collectSpine (a, k, vars, depth) = match a with
    | I.Nil -> (k, vars)
    | I.App (u, s) ->
        let k', vars' = collectExp (u, k, vars, depth) in
        collectSpine (s, k', vars', depth)

  and collectExp (a, k_, vars, depth) = match a with
    | I.Root ((I.BVar k as h), s) ->
        let k', vars', replaced = collectHead (h, s, k_, vars, depth) in
        begin if replaced then (k', vars')
        else collectSpine (s, k', vars', depth)
        end
    | (I.Root (I.Def k, s) as u) ->
        ((depth, Def k) :: k_, vars)
    | I.Root (h, s) -> collectSpine (s, k_, vars, depth)
    | I.Lam (d, u) -> collectExp (u, k_, vars, depth + 1)
    | I.FgnExp (cs, fe) -> ((depth, Fgn) :: k_, vars)

  (* don't collect D, since it is ignored in unification *)
  (* | collectExp (I.Uni(L), K, Vars, depth) = (K, Vars) *)
  (* should be impossible, Mon Apr 15 14:55:15 2002 -fp *)
  (* h is either const or skonst of def*)

  (* no EVars, since U in NF *)
  (* shiftHead (H, depth, total) = H'
     shiftExp (U, depth, total) = U'
     shiftSpine (S, depth, total) = S'

     where each variable k > depth is shifted by +total

     Invariants: U is NF, S is in NF
  *)
  let shiftHead (a, depth, total) = match a with
    | (I.BVar k as h) ->
        begin if k > depth then I.BVar (k + total) else I.BVar k
        end
    | (I.Const k as h) -> h
    | (I.Def k as h) -> h
    | (I.NSDef k as h) -> h
    | (I.FgnConst _ as h) -> h
    | (I.Skonst k as h) -> h

  let rec shiftExp (a, depth, total) = match a with
    | I.Root (h, s) ->
        I.Root (shiftHead (h, depth, total), shiftSpine (s, depth, total))
    | I.Uni l -> I.Uni l
    | I.Lam (d, u) ->
        I.Lam (shiftDec (d, depth, total), shiftExp (u, depth + 1, total))
    | I.Pi ((d, p), u) ->
        I.Pi ((shiftDec (d, depth, total), p), shiftExp (u, depth + 1, total))
    | I.FgnExp (csfe1, csfe2) ->
        I.FgnExpStd.Map.apply csfe1 csfe2 (function u ->
            shiftExp (Whnf.normalize (u, I.id), depth, total))
  (* Tue Apr  2 12:10:24 2002 -fp -bp *)
  (* this is overkill and could be very expensive for deeply nested foreign exps *)
  (* calling normalize here because U may not be normal *)

  and shiftSpine (a, depth, total) = match a with
    | I.Nil -> I.Nil
    | I.App (u, s) ->
        I.App (shiftExp (u, depth, total), shiftSpine (s, depth, total))

  and shiftDec (I.Dec (x, v), depth, total) =
    I.Dec (x, shiftExp (v, depth, total))

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
  *)
  let linearHead (g, a, s, left, vars, depth, total) = match a with
    | (I.BVar k as h) ->
        begin if k > depth then
          begin if etaSpine (s, depth) then
            begin if seen (k - depth, vars) then
              (left - 1, vars, I.BVar (left + depth), true)
            else (left, (depth, k - depth) :: vars, I.BVar (k + total), false)
            end
          else (left - 1, vars, I.BVar (left + depth), true)
          end
        else (left, vars, h, false)
        end
    | (I.Const k as h) ->
        (left, vars, h, false)
    | (I.FgnConst (k, conDec) as h) ->
        (left, vars, h, false)
    | (I.Skonst k as h) ->
        (left, vars, h, false)
  (*
     | linearHead(G, (h as I.NSDef k), s, S, left, Vars, depth, total) =
         (left, Vars, h, false)
     *)

  (* Def cannot occur *)
  (* linearExp (Gl, U, left, Vars, depth, total, eqns) = (left', Vars', N, Eqn)

     call linearHead on every embedded root

     left' = left - #replaced expressions in U
     Vars' = all BVars in G0 seen in U
     N = copy of U with replaced expressions
     Eqn = residual equations

     ""For any U', U = U' iff (N = U' and Eqn)""
  *)
  let rec linearExp (gl, a, left, vars, depth, total, eqns) = match a with
    | (I.Root ((I.Def k as h), s) as u)
      ->
        let n = I.Root (I.BVar (left + depth), I.Nil) in
        let u' = shiftExp (u, depth, total) in
        (left - 1, vars, n, C.UnifyEq (gl, u', n, eqns))
    | (I.Root (h, s) as u) ->
        let left', vars', h', replaced =
          linearHead (gl, h, s, left, vars, depth, total)
        in
        begin if replaced then
          let n = I.Root (h', I.Nil) in
          let u' = shiftExp (u, depth, total) in
          (left', vars, n, C.UnifyEq (gl, u', n, eqns))
        else
          let left'', vars'', s', eqns' =
            linearSpine (gl, s, left', vars', depth, total, eqns)
          in
          (left'', vars'', I.Root (h', s'), eqns')
        end
        (* h = h' not replaced *)
    | I.Lam (d, u) ->
        let d' = shiftDec (d, depth, total) in
        let left', vars', u', eqns' =
          linearExp (I.Decl (gl, d'), u, left, vars, depth + 1, total, eqns)
        in
        (left', vars', I.Lam (d', u'), eqns')
    | (I.FgnExp (cs, ops) as u) ->
        let n = I.Root (I.BVar (left + depth), I.Nil) in
        let u' = shiftExp (u, depth, total) in
        (left - 1, vars, n, C.UnifyEq (gl, u', n, eqns))
  (*
     | linearExp (Gl, U as I.Uni(L), left, Vars, depth, total, eqns) =
         (left, Vars, I.Uni(L), eqns)
     *)

  (* should be impossible  Mon Apr 15 14:54:42 2002 -fp *)
  and linearSpine (gl, a, left, vars, depth, total, eqns) = match a with
    | I.Nil -> (left, vars, I.Nil, eqns)
    | I.App (u, s) ->
        let left', vars', u', eqns' =
          linearExp (gl, u, left, vars, depth, total, eqns)
        in
        let left'', vars'', s', eqns'' =
          linearSpine (gl, s, left', vars', depth, total, eqns')
        in
        (left'', vars'', I.App (u', s'), eqns'')

  (* SClo(S, s') cannot occur *)
  (*  compileLinearHead (G, R as I.Root (h, S)) = r

       r is residual goal
       if G |- R and R might not be linear

       then

           G |- H ResGoal  and H is linear
       and of the form
           (Axists(_ , Axists( _, ....., Axists( _, Assign (E, AuxG)))))
  *)
  let compileLinearHead (g, (I.Root (h, s) as r_)) =
    let k_, _ = collectExp (r_, [], [], 0) in
    let left = List.length k_ in
    let left', _, r', eqs =
      linearExp (I.Null, r_, left, [], 0, left, C.Trivial)
    in
    let rec convertKRes (resG, a, i) = match a, i with
      | [], 0 -> resG
      | (d, k) :: k_, i ->
          C.Axists
            ( I.ADec (Some ("A" ^ Int.toString i), d),
              convertKRes (resG, k_, i - 1) )
    in
    let r = convertKRes (C.Assign (r', eqs), List.rev k_, left) in
    Display.chatter_s 6 "\nClause LH Eqn";
    Display.chatter_s 6 (CPrint.clauseToString "\t" (g, r));
    r

  (*  compileSbtHead (G, R as I.Root (h, S)) = r

       r is residual goal
       if G |- R and R might not be linear

       then

           G |- H ResGoal  and H is linear

  *)
  let compileSbtHead (g, (I.Root (h, s) as h_)) =
    let k_, _ = collectExp (h_, [], [], 0) in
    let left = List.length k_ in
    let left', _, h', eqs =
      linearExp (I.Null, h_, left, [], 0, left, C.Trivial)
    in
    let rec convertKRes (g, a, i) = match a, i with
      | [], 0 -> g
      | (d, k) :: k_, i ->
          convertKRes
            (I.Decl (g, I.ADec (Some ("AVar " ^ Int.toString i), d)), k_, i - 1)
    in
    let g' = convertKRes (g, List.rev k_, left) in
    Display.chatter_s 6 "\nClause Sbt Eqn";
    Display.chatter_s 6
      (CPrint.clauseToString "\t" (g', C.Assign (h', eqs)));
    (g', Some (h', eqs))
  (* insert R' together with Eqs and G and sc C.True *)

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
  *)
  let rec compileGoalN arg__1 arg__2 =
    begin match (arg__1, arg__2) with
    | fromCS, (g, (I.Root _ as r)) -> C.Atom r
    | fromCS, (g, I.Pi ((I.Dec (_, a1), I.No), a2)) ->
        let ha1 = I.targetHead a1 in
        let r = compileDClauseN fromCS false (g, a1) in
        let goal = compileGoalN fromCS (I.Decl (g, I.Dec (None, a1)), a2) in
        C.Impl (r, a1, ha1, goal)
        (* A1 is used to build the proof term, Ha1 for indexing *)
        (* never optimize when compiling local assumptions *)
    | fromCS, (g, I.Pi (((I.Dec (_, a1) as d), I.Maybe), a2)) ->
        begin if notCS fromCS && isConstraint (head a1) then
          raise (Error "Constraint appears in dynamic clause position")
        else C.All (d, compileGoalN fromCS (I.Decl (g, d), a2))
        end
    end
  (* A = {x:A1} A2 *)
  (* A = A1 -> A2 *)
  (* A = H @ S *)

  and compileGoal fromCS (g, (a, s)) =
    compileGoalN fromCS (g, Whnf.normalize (a, s))

  and compileDClauseN arg__3 arg__4 arg__5 =
    begin match (arg__3, arg__4, arg__5) with
    | fromCS, opt, (g, (I.Root (h, s) as r)) ->
        begin if opt && !optimize = C.LinearHeads then compileLinearHead (g, r)
        else
          begin if notCS fromCS && isConstraint h then
            raise (Error "Constraint appears in dynamic clause position")
          else C.Eq r
          end
        end
    | fromCS, opt, (g, I.Pi (((I.Dec (_, a1) as d), I.No), a2)) ->
        C.And
          ( compileDClauseN fromCS opt (I.Decl (g, d), a2),
            a1,
            compileGoalN fromCS (g, a1) )
    | fromCS, opt, (g, I.Pi ((d, I.Maybe), a2)) ->
        C.Exists (d, compileDClauseN fromCS opt (I.Decl (g, d), a2))
    | fromCS, opt, (g, I.Pi (((I.Dec (_, a1) as d), I.Meta), a2)) ->
        C.In
          ( compileDClauseN fromCS opt (I.Decl (g, d), a2),
            a1,
            compileGoalN fromCS (g, a1) )
    end

  (* A = {x:A1} A2 *)
  (* A = {x: A1} A2, x  meta variable occuring in A2 *)
  (* A = A1 -> A2 *)

  (*  compileGoalN _ should not arise by invariants *)
  (* compileDClause A => G (top level)
     if A is a type interpreted as a clause and G is its compiled form.

     Some optimization is attempted if so flagged.

     Invariants:
     If G |- A : type, A enf
        A has no existential type variables
     then G |- A ~> r  (A compiles to residual goal r)
     and  G |- r  resgoal
  *)
  (*  compileDClauseN _ should not arise by invariants *)
  (* Compilation of (static) program clauses *)
  (* compileSubgoals G' (n, Stack, G) = Subgoals  (top level)

     Invariants:
     If G : Stack
        G' ctx where G' = G, GAVar
     then Stack ~> subgoals  (Stack compiles to subgoals)
     and  G' |- subgoals
  *)
  let rec compileSubgoals arg__6 arg__7 arg__8 =
    begin match (arg__6, arg__7, arg__8) with
    | fromCS, g', (n, I.Decl (stack, I.No), I.Decl (g, I.Dec (_, a))) ->
        let sg = compileSubgoals fromCS g' (n + 1, stack, g) in
        C.Conjunct
          ( compileGoal fromCS (g', (a, I.Shift (n + 1))),
            I.EClo (a, I.Shift (n + 1)),
            sg )
        (* G |- A and G' |- A[^(n+1)] *)
    | fromCS, g', (n, I.Decl (stack, I.Maybe), I.Decl (g, I.Dec (_, a1))) ->
        compileSubgoals fromCS g' (n + 1, stack, g)
    | fromCS, g', (n, I.Null, I.Null) -> C.True
    end

  (* compileSClause (Stack, G, A) => (Head, SubGoals) (top-level)
     if A is a type interpreted as a clause and (Head, SubGoals)
     is its compiled form.

     Invariants:
     If G |- A : type, A enf
        A has no existential type variables
     then G |- A ~> (Head, subgoals) ((A compiles to head and subgoals)
          where GAVar, G |- Head and GAVar, G |- subgoals
          and Head is linear and G' = GAVar, G
  *)
  let rec compileSClauseN arg__9 arg__10 =
    begin match (arg__9, arg__10) with
    | fromCS, (stack, g, (I.Root (h, s) as r)) ->
        let g', head = compileSbtHead (g, r) in
        let d = I.ctxLength g' - I.ctxLength g in
        let sgoals = compileSubgoals fromCS g' (d, stack, g) in
        ((g', head), sgoals)
        (* G' |- Sgoals  and G' |- ^d : G *)
    | fromCS, (stack, g, I.Pi (((I.Dec (_, a1) as d), I.No), a2)) ->
        compileSClauseN fromCS (I.Decl (stack, I.No), I.Decl (g, d), a2)
    | fromCS, (stack, g, I.Pi (((I.Dec (_, a1) as d), meta), a2)) ->
        compileSClauseN fromCS (I.Decl (stack, I.Meta), I.Decl (g, d), a2)
    | fromCS, (stack, g, I.Pi (((I.Dec (_, a1) as d), I.Maybe), a2)) ->
        compileSClauseN fromCS (I.Decl (stack, I.Maybe), I.Decl (g, d), a2)
    end

  let compileDClause opt (g, a) =
    compileDClauseN I.Ordinary opt (g, Whnf.normalize (a, I.id))

  let compileGoal g a =
    compileGoalN I.Ordinary (g, Whnf.normalize (a, I.id))

  (* compileCtx G = (G, dPool)

     Invariants:
     If |- G ctx,
     then |- G ~> dPool  (context G compile to clause pool dPool)
     and  |- dPool  dpool
  *)
  let compileCtx opt g =
    let rec compileBlock = function
      | [], s, (n, i) -> []
      | I.Dec (_, v) :: vs, t, (n, i) ->
          let vt = I.EClo (v, t) in
          (compileDClause opt (g, vt), I.id, I.targetHead vt)
          :: compileBlock
               ( vs,
                 I.Dot (I.Exp (I.Root (I.Proj (I.Bidx n, i), I.Nil)), t),
                 (n, i + 1) )
    in
    let rec compileCtx' =
      let open CompSyn in
      function
      | I.Null -> I.Null
      | I.Decl (g, I.Dec (_, a)) ->
          let ha = I.targetHead a in
          I.Decl
            (compileCtx' g, CompSyn.Dec (compileDClause opt (g, a), I.id, ha))
      | I.Decl (g, I.BDec (_, (c, s))) ->
          let g, l = I.constBlock c in
          let dpool = compileCtx' g in
          let n = I.ctxLength dpool in
          I.Decl (dpool, CompSyn.BDec (compileBlock (l, s, (n, 1))))
      (* this is inefficient! -cs *)
    in
    C.DProg (g, compileCtx' g)

  (* compile G = (G, dPool)

     Invariants:
     If |- G ctx,
     then |- G ~> dPool  (context G compile to clause pool dPool)
     and  |- dPool  dpool
  *)
  let compilePsi opt psi =
    let rec compileBlock = function
      | [], s, (n, i) -> []
      | I.Dec (_, v) :: vs, t, (n, i) ->
          let vt = I.EClo (v, t) in
          (compileDClause opt (T.coerceCtx psi, vt), I.id, I.targetHead vt)
          :: compileBlock
               ( vs,
                 I.Dot (I.Exp (I.Root (I.Proj (I.Bidx n, i), I.Nil)), t),
                 (n, i + 1) )
    in
    let rec compileCtx' = function
      | I.Null -> I.Null
      | I.Decl (g, I.Dec (_, a)) ->
          let ha = I.targetHead a in
          I.Decl
            (compileCtx' g, CompSyn.Dec (compileDClause opt (g, a), I.id, ha))
      | I.Decl (g, I.BDec (_, (c, s))) ->
          let g, l = I.constBlock c in
          let dpool = compileCtx' g in
          let n = I.ctxLength dpool in
          I.Decl (dpool, CompSyn.BDec (compileBlock (l, s, (n, 1))))
      (* this is inefficient! -cs *)
    in
    let rec compilePsi' = function
      | I.Null -> I.Null
      | I.Decl (psi, T.UDec (I.Dec (_, a))) ->
          let ha = I.targetHead a in
          I.Decl
            ( compilePsi' psi,
              CompSyn.Dec (compileDClause opt (T.coerceCtx psi, a), I.id, ha)
            )
      | I.Decl (psi, T.UDec (I.BDec (_, (c, s)))) ->
          let g, l = I.constBlock c in
          let dpool = compileCtx' g in
          let n = I.ctxLength dpool in
          I.Decl (dpool, CompSyn.BDec (compileBlock (l, s, (n, 1))))
          (* this is inefficient! -cs *)
      | I.Decl (psi, T.PDec _) -> I.Decl (compilePsi' psi, CompSyn.PDec)
    in
    C.DProg (T.coerceCtx psi, compilePsi' psi)

  (* installClause fromCS (a, A) = ()
     Effect: compiles and installs compiled form of A according to
             the specified compilation strategy
  *)
  let installClause fromCS (a, a_) =
    begin match !C.optimize with
    | No ->
        C.sProgInstall (a, C.SClause (compileDClauseN fromCS true (I.Null, a_)))
    | LinearHeads ->
        C.sProgInstall (a, C.SClause (compileDClauseN fromCS true (I.Null, a_)))
    | Indexing ->
        let (g, head), r =
          compileSClauseN fromCS (I.Null, I.Null, Whnf.normalize (a_, I.id))
        in
        ignore (C.sProgInstall
            (a, C.SClause (compileDClauseN fromCS true (I.Null, a_))));
        begin match head with
        | None -> raise (Error "Install via normal index")
        | Some (h, eqs) ->
            SubTree.sProgInstall
              (cidFromHead (I.targetHead a_), C.Head (h, g, eqs, a), r)
        end
    end

  (* compileConDec (a, condec) = ()
     Effect: install compiled form of condec in program Table.
             No effect if condec has no operational meaning
  *)
  (* Defined constants are currently not compiled *)
  let compileConDec arg__11 arg__12 =
    begin match (arg__11, arg__12) with
    | fromCS, (a, I.ConDec (_, _, _, _, a_, Type)) ->
        installClause fromCS (a, a_)
    | fromCS, (a, I.SkoDec (_, _, _, a_, Type)) ->
        begin match !C.optimize with
        | No ->
            C.sProgInstall
              (a, C.SClause (compileDClauseN fromCS true (I.Null, a_)))
        | _ ->
            C.sProgInstall
              (a, C.SClause (compileDClauseN fromCS true (I.Null, a_)))
        end
    | I.Clause, (a, I.ConDef (_, _, _, _, a_, I.Type, _)) ->
        C.sProgInstall
          ( a,
            C.SClause
              (compileDClauseN I.Clause true
                 (I.Null, Whnf.normalize (a_, I.id))) )
    | _, _ -> ()
    end
  (* we don't use substitution tree indexing for skolem constants yet -bp*)

  let install fromCS cid = compileConDec fromCS (cid, I.sgnLookup cid)

  let sProgReset () =
    begin
      SubTree.sProgReset ();
      C.sProgReset ()
    end
end

(*! sharing Names.IntSyn = IntSyn' !*)
(* local open ... *)
(* functor Compile *)
(* # 1 "src/compile/Compile_.sml.ml" *)

(* Now in compsyn.fun *)
(*
structure CompSyn =
  CompSyn (structure Global = Global
           ! structure IntSyn' = IntSyn !
	   structure Names = Names
           structure Table = IntRedBlackTree);
*)
module CPrint = Cprint.Make_CPrint (Print) (Formatter) (Names)

module SubTree = Subtree.SubTree (struct
  module IntSyn' = IntSyn
  module Whnf = Whnf
  module Unify = UnifyTrail
  module CompSyn' = CompSyn
  module Print = Print
  module CPrint = CPrint
  module Names = Names
  module Formatter = Formatter
  module CsManager = CsManager
  module Table = IntRedBlackTree
  module RBSet = RBSet
end)

module Compile =
  MakeCompile (Whnf) (TypeCheck) (SubTree) (CPrint) (Print) (Names)

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
