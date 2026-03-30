(* # 1 "src/opsem/subtree_inst.sig.ml" *)

(* # 1 "src/opsem/subtree_inst.fun.ml" *)
open! Basis
open Abstract_tabled
open Memo_table

(* Linear Substitution Tree indexing *)
(* Linearity: Any variables occurring inside the substitution tree are linear *)
(* Any term we insert into the substitution tree is in normalform ! *)
(* Instance Checking *)
(* Author: Brigitte Pientka *)
module MemoTableInst (MemoTableInst__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn' !*)
  module Whnf : WHNF
  module Match : MATCH

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  (*! structure RBSet : RBSET !*)
  module Assign : ASSIGN

  (*! structure TableParam : TABLEPARAM !*)
  (*! sharing TableParam.IntSyn = IntSyn' !*)
  (*! sharing TableParam.CompSyn = CompSyn' !*)
  (*! sharing TableParam.RBSet = RBSet !*)
  module AbstractTabled : ABSTRACTTABLED

  (*! sharing AbstractTabled.IntSyn = IntSyn' !*)
  module Print : PRINT
end) : MEMOTABLE = struct
  open MemoTableInst__0
  open! Red_black_set
  open! Table_param

  (*! structure IntSyn = IntSyn' !*)
  (* ---------------------------------------------------------------------- *)
  (* Linear substitution tree for linear terms *)
  (* normalSubsts: key = int = nvar  (key, (depth, U))

   example:  \x. f( i1, a)   then i1 = (1, X) = X[x/x]

   *)
  (* property: linear *)
  type nonrec normalSubsts = (int * IntSyn.exp) RBSet.ordSet (* local depth *)
  type nonrec exSubsts = IntSyn.front RBSet.ordSet

  let nid : unit -> normalSubsts = RBSet.new_
  let asid : unit -> exSubsts = RBSet.new_
  let aid = TableParam.aid
  let rec isId s = RBSet.isEmpty s

  (* ---------------------------------------------------------------------- *)
  (* Context for existential variable *)
  type nonrec ctx = (int * IntSyn.dec) list ref

  (* functions for handling context for existential variables *)
  let rec emptyCtx () = (ref [] : ctx)
  let rec copy l_ = (ref !l_ : ctx)

  (* destructively updates L *)
  let rec delete (x, (l_ : ctx)) =
    let rec del = function
      | x, [], l_ -> None
      | x, ((y, e_) as h_) :: l_, l'_ -> begin
          if x = y then Some ((y, e_), rev l'_ @ l_) else del (x, l_, h_ :: l'_)
        end
    in
    begin match del (x, !l_, []) with
    | None -> None
    | Some ((y, e_), l'_) -> begin
        l_ := l'_;
        Some (y, e_)
      end
    end

  let rec member (x, (l_ : ctx)) =
    let rec memb = function
      | x, [] -> None
      | x, ((y, (IntSyn.Dec (n, u_) as e_)) :: l_ as h_) -> begin
          if x = y then Some (y, e_) else memb (x, l_)
        end
      | x, ((y, (IntSyn.ADec (n, d) as e_)) :: l_ as h_) -> begin
          if x = y then Some (y, e_) else memb (x, l_)
        end
    in
    memb (x, !l_)

  let rec insertList (e_, l_) = l_ := e_ :: !l_

  (* ---------------------------------------------------------------------- *)
  (* Substitution Tree *)
  (* It is only possible to distribute the evar-ctx because
     all evars occur exactly once, i.e. they are linear.
     This allows us to maintain invariant, that every occurrence of an evar is
     defined in its evar-ctx
  *)
  type tree =
    | Leaf of
        (ctx * normalSubsts)
        * ((int * int)
          * ctx
          * IntSyn.dctx
          * TableParam.resEqn
          * TableParam.answer
          * int
          * TableParam.status)
          list
          ref
    (* G *)
    (* D *)
    (* #G *)
    (* #EVar *)
    | Node of (ctx * normalSubsts) * tree ref list

  let rec makeTree () = ref (Node ((emptyCtx (), nid ()), []))
  let rec noChildren c_ = c_ = []

  type retrieval = Variant of int * IntSyn.exp | NotCompatible

  type compSub =
    | SplitSub of
        (ctx * normalSubsts) * (ctx * normalSubsts) * (ctx * normalSubsts)
    (* rho2 *)
    (* rho1 *)
    (* sigma *)
    | InstanceSub of exSubsts * (ctx * normalSubsts (* rho2 *))
    | VariantSub of ctx * normalSubsts (* rho2 *)
    | NoCompatibleSub

  (* Index array

   All type families have their own substitution tree and all substitution trees
   are stored in an array [a1,...,an]   where ai is a substitution tree for type family ai
   *)
  let indexArray =
    Array.tabulate (Global.maxCid, function i -> (ref 0, makeTree ()))

  exception Error of string

  open! struct
    module I = IntSyn
    module C = CompSyn
    module S = RBSet
    module A = AbstractTabled
    module T = TableParam

    exception Assignment of string
    exception Instance of string
    exception Generalization of string
    exception DifferentSpines

    let rec emptyAnswer () = T.emptyAnsw ()
    let answList : TableParam.answer list ref = ref []
    let added = ref false

    type nonrec nvar = int
    type nonrec bvar = int
    type nonrec bdepth = int

    let rec expToS (g_, u_) = try Print.expToString (g_, u_) with _ -> " <_ >"

    let rec printSub = function
      | g_, I.Shift n -> print (("I.Shift " ^ Int.toString n) ^ "\n")
      | g_, I.Dot (I.Idx n, s) -> begin
          print (("Idx " ^ Int.toString n) ^ " . ");
          printSub (g_, s)
        end
      | g_, I.Dot (I.Exp (I.EVar ({ contents = Some u_ }, _, _, _) as x_), s) ->
        begin
          print (("Exp ( EVar " ^ expToS (g_, x_)) ^ ").");
          printSub (g_, s)
        end
      | g_, I.Dot (I.Exp (I.EVar (_, _, _, _) as x_), s) -> begin
          print (("Exp ( EVar  " ^ expToS (g_, x_)) ^ ").");
          printSub (g_, s)
        end
      | g_, I.Dot (I.Exp (I.AVar _), s) -> begin
          print "Exp (AVar _ ). ";
          printSub (g_, s)
        end
      | g_, I.Dot (I.Exp (I.EClo (I.AVar { contents = Some u_ }, s')), s) ->
        begin
          print (("Exp (AVar " ^ expToS (g_, I.EClo (u_, s'))) ^ ").");
          printSub (g_, s)
        end
      | ( g_,
          I.Dot
            ( I.Exp (I.EClo (I.EVar ({ contents = Some u_ }, _, _, _), s') as x_),
              s ) ) -> begin
          print (("Exp (EVarClo " ^ expToS (g_, I.EClo (u_, s'))) ^ ") ");
          printSub (g_, s)
        end
      | g_, I.Dot (I.Exp (I.EClo (u_, s') as x_), s) -> begin
          print (("Exp (EClo " ^ expToS (g_, Whnf.normalize (u_, s'))) ^ ") ");
          printSub (g_, s)
        end
      | g_, I.Dot (I.Exp e_, s) -> begin
          print (("Exp ( " ^ expToS (g_, e_)) ^ " ). ");
          printSub (g_, s)
        end
      | g_, I.Dot (I.Undef, s) -> begin
          print "Undef . ";
          printSub (g_, s)
        end

    let rec normalizeSub = function
      | I.Shift n -> I.Shift n
      | I.Dot (I.Exp (I.EClo (I.AVar { contents = Some u_ }, s')), s) ->
          I.Dot (I.Exp (Whnf.normalize (u_, s')), normalizeSub s)
      | I.Dot (I.Exp (I.EClo (I.EVar ({ contents = Some u_ }, _, _, _), s')), s)
        ->
          I.Dot (I.Exp (Whnf.normalize (u_, s')), normalizeSub s)
      | I.Dot (I.Exp u_, s) ->
          I.Dot (I.Exp (Whnf.normalize (u_, I.id)), normalizeSub s)
      | I.Dot (I.Idx n, s) -> I.Dot (I.Idx n, normalizeSub s)

    let rec etaSpine = function
      | I.Nil, n -> n = 0
      | I.App (I.Root (I.BVar k, I.Nil), s_), n -> k = n && etaSpine (s_, n - 1)
      | I.App (a_, s_), n -> false

    let cidFromHead = function I.Const c -> c | I.Def c -> c
    let rec dotn = function 0, s -> s | i, s -> dotn (i - 1, I.dot1 s)

    let rec raiseType = function
      | I.Null, v_ -> v_
      | I.Decl (g_, d_), v_ -> raiseType (g_, I.Lam (d_, v_))

    let rec compose = function
      | I.Null, g_ -> g_
      | IntSyn.Decl (g'_, d_), g_ -> IntSyn.Decl (compose (g'_, g_), d_)

    let rec shift = function
      | I.Null, s -> s
      | IntSyn.Decl (g_, d_), s -> I.dot1 (shift (g_, s))

    let rec ctxToEVarSub = function
      | I.Null, s -> s
      | I.Decl (g_, I.Dec (_, a_)), s ->
          let x_ = I.newEVar (I.Null, a_) in
          I.Dot (I.Exp x_, ctxToEVarSub (g_, s))

    let rec lowerEVar' = function
      | x_, g_, (I.Pi ((d'_, _), v'_), s') ->
          let d''_ = I.decSub (d'_, s') in
          let x'_, u_ =
            lowerEVar' (x_, I.Decl (g_, d''_), Whnf.whnf (v'_, I.dot1 s'))
          in
          (x'_, I.Lam (d''_, u_))
      | x_, g_, vs'_ ->
          let x'_ = x_ in
          (x'_, x'_)

    and lowerEVar1 = function
      | x_, I.EVar (r, g_, _, _), ((I.Pi _ as v_), s) ->
          let x'_, u_ = lowerEVar' (x_, g_, (v_, s)) in
          I.EVar (ref (Some u_), I.Null, v_, ref [])
      | _, x_, _ -> x_

    and lowerEVar = function
      | e_, (I.EVar (r, g_, v_, { contents = [] }) as x_) ->
          lowerEVar1 (e_, x_, Whnf.whnf (v_, I.id))
      | e_, I.EVar _ ->
          raise
            (Error
               "abstraction : LowerEVars: Typing ambiguous -- constraint of \
                functional type cannot be simplified")

    let rec ctxToAVarSub = function
      | g'_, I.Null, s -> s
      | g'_, I.Decl (d_, I.Dec (_, a_)), s ->
          let (I.EVar (r, _, _, cnstr) as e_) = I.newEVar (I.Null, a_) in
          I.Dot (I.Exp e_, ctxToAVarSub (g'_, d_, s))
      | g'_, I.Decl (d_, I.ADec (_, d)), s ->
          let x_ = I.newAVar () in
          I.Dot (I.Exp (I.EClo (x_, I.Shift (-d))), ctxToAVarSub (g'_, d_, s))

    let rec assign = function
      | d, (I.Dec (n, v_) as dec1_), (I.Root (I.BVar k, s1_) as e1_), u_, asub
        ->
          let (I.EVar (r, _, _, cnstr) as e_) = I.newEVar (I.Null, v_) in
          let x_ =
            lowerEVar1 (e_, I.EVar (r, I.Null, v_, cnstr), Whnf.whnf (v_, I.id))
          in
          let _ = r := Some u_ in
          S.insert asub (k - d, I.Exp x_)
      | d, (I.ADec (n, d') as dec1_), (I.Root (I.BVar k, s1_) as e1_), u_, asub
        ->
          let (I.AVar r as a_) = I.newAVar () in
          let _ = r := Some u_ in
          let us_ = Whnf.whnf (u_, I.Shift (-d')) in
          S.insert asub (k - d, I.Exp (I.EClo (a_, I.Shift (-d'))))

    let rec assignExp = function
      | ( fasub,
          (((r, passed) as ctxTotal), d),
          (d1_, (I.Root (h1_, s1_) as u1_)),
          (d2_, (I.Root (h2_, s2_) as u2_)) ) -> begin
          match (h1_, h2_) with
          | I.Const c1, I.Const c2 -> begin
              if c1 = c2 then
                assignSpine (fasub, (ctxTotal, d), (d1_, s1_), (d2_, s2_))
              else raise (Assignment "Constant clash")
            end
          | I.Def c1, I.Def c2 -> begin
              if c1 = c2 then
                assignSpine (fasub, (ctxTotal, d), (d1_, s1_), (d2_, s2_))
              else
                let u1'_ = Whnf.normalize (Whnf.expandDef (u1_, I.id)) in
                let u2'_ = Whnf.normalize (Whnf.expandDef (u2_, I.id)) in
                assignExp (fasub, (ctxTotal, d), (d1_, u1'_), (d2_, u2'_))
            end
          | I.Def c1, _ ->
              let u1'_ = Whnf.normalize (Whnf.expandDef (u1_, I.id)) in
              assignExp (fasub, (ctxTotal, d), (d1_, u1'_), (d2_, u2_))
          | _, I.Def c2 ->
              let u2'_ = Whnf.normalize (Whnf.expandDef (u2_, I.id)) in
              assignExp (fasub, (ctxTotal, d), (d1_, u1_), (d2_, u2'_))
          | I.BVar k1, I.BVar k2 -> begin
              if k1 <= r + d then begin
                if k2 <= r + d then begin
                  if k2 = k1 then fasub else raise (Assignment "BVar clash")
                end
                else raise (Assignment "BVar - EVar clash")
              end
              else begin
                match member (k1 - d + passed, d1_) with
                | None -> raise (Assignment "EVar nonexistent")
                | Some (x, dec_v) -> begin
                    if k2 <= r + d then raise (Assignment "EVar - BVar clash")
                    else begin
                      if k2 = k1 then function
                        | asub -> begin
                            fasub asub;
                            assign (d, dec_v, u1_, u2_, asub)
                          end
                      else
                        raise
                          (Assignment
                             "EVars are different -- outside of the allowed \
                              fragment")
                    end
                  end
              end
            end
          | I.Skonst c1, I.Skonst c2 -> begin
              if c1 = c2 then
                assignSpine (fasub, (ctxTotal, d), (d1_, s1_), (d2_, s2_))
              else raise (Assignment "Skolem constant clash")
            end
          | _ -> raise (Assignment "Head mismatch ")
        end
      | ( fasub,
          (ctxTotal, d),
          (d1_, I.Lam (dec1_, u1_)),
          (d2_, I.Lam (dec2_, u2_)) ) ->
          assignExp (fasub, (ctxTotal, d + 1), (d1_, u1_), (d2_, u2_))
      | ( fasub,
          (ctxTotal, d),
          (d1_, I.Pi (((I.Dec (_, v1_) as dec1_), _), u1_)),
          (d2_, I.Pi (((I.Dec (_, v2_) as dec2_), _), u2_)) ) ->
          let fasub' =
            assignExp (fasub, (ctxTotal, d), (d1_, v1_), (d2_, v2_))
          in
          assignExp (fasub', (ctxTotal, d + 1), (d1_, u1_), (d2_, u2_))
      | fasub, (ctxTotal, d), (d1_, I.EClo (u_, (I.Shift 0 as s'))), (d2_, u2_)
        ->
          assignExp (fasub, (ctxTotal, d), (d1_, u_), (d2_, u2_))
      | fasub, (ctxTotal, d), (d1_, u1_), (d2_, I.EClo (u_, (I.Shift 0 as s)))
        ->
          assignExp (fasub, (ctxTotal, d), (d1_, u1_), (d2_, u_))

    and assignSpine = function
      | fasub, (ctxTotal, d), (d1_, I.Nil), (d2_, I.Nil) -> fasub
      | fasub, (ctxTotal, d), (d1_, I.App (u1_, s1_)), (d2_, I.App (u2_, s2_))
        ->
          let fasub' =
            assignExp (fasub, (ctxTotal, d), (d1_, u1_), (d2_, u2_))
          in
          assignSpine (fasub', (ctxTotal, d), (d1_, s1_), (d2_, s2_))

    let rec assignCtx = function
      | fasub, ctxTotal, (d1_, I.Null), (d2_, I.Null) -> fasub
      | ( fasub,
          ((r, passed) as ctxTotal),
          (d1_, I.Decl (g1_, I.Dec (_, v1_))),
          (d2_, I.Decl (g2_, I.Dec (_, v2_))) ) ->
          let fasub' =
            assignExp (fasub, ((r - 1, passed + 1), 0), (d1_, v1_), (d2_, v2_))
          in
          assignCtx (fasub', (r - 1, passed + 1), (d1_, g1_), (d2_, g2_))

    let nctr = ref 1

    let rec newNVar () =
      begin
        nctr := !nctr + 1;
        I.NVar !nctr
      end

    let rec equalDec = function
      | I.Dec (_, u_), I.Dec (_, u'_) -> Conv.conv ((u_, I.id), (u'_, I.id))
      | I.ADec (_, d), I.ADec (_, d') -> d = d'
      | _, _ -> false

    let rec equalCtx = function
      | I.Null, s, I.Null, s' -> true
      | ( I.Decl (g_, (I.Dec (_, a_) as d_)),
          s,
          I.Decl (g'_, (I.Dec (_, a'_) as d'_)),
          s' ) ->
          Conv.convDec ((d_, s), (d'_, s'))
          && equalCtx (g_, I.dot1 s, g'_, I.dot1 s')
      | _, s, _, s' -> false

    let rec equalEqn = function
      | T.Trivial, T.Trivial -> true
      | T.Unify (g_, x_, n_, eqn), T.Unify (g'_, x'_, n'_, eqn') ->
          equalCtx (g_, I.id, g'_, I.id)
          && Conv.conv ((x_, I.id), (x'_, I.id))
          && Conv.conv ((n_, I.id), (n'_, I.id))
          && equalEqn (eqn, eqn')
      | _, _ -> false

    let rec equalEqn' = function
      | d, (d_, T.Trivial), (d'_, T.Trivial), asub -> true
      | ( d,
          (d_, T.Unify (g_, (I.Root (I.BVar k, s_) as x_), n_, eqn)),
          (d'_, T.Unify (g'_, x'_, n'_, eqn')),
          asub ) -> begin
          if
            equalCtx (g_, I.id, g'_, I.id)
            && Conv.conv ((x_, I.id), (x'_, I.id))
            && Conv.conv ((n_, I.id), (n'_, I.id))
          then
            let d' = d + I.ctxLength g'_ in
            begin
              begin if k - d' > 0 then begin
                match member (k - d', d'_) with
                | None -> ()
                | Some (x, dec_v) -> begin
                    match RBSet.lookup asub (k - d') with
                    | None -> begin
                        ignore (delete (x, d'_));
                        ignore (S.insert asub (k - d', I.Idx (k - d')))
                      end
                    | Some _ -> ()
                  end
              end
              else begin
                print "Impossible -- Found BVar instead of EVar\n";
                raise (Error "Impossibe -- Found BVar instead of EVar ")
              end
              end;
              equalEqn' (d, (d_, eqn), (d'_, eqn'), asub)
            end
          else false
        end
      | d, _, _, asub -> false

    let rec equalSub = function
      | I.Shift k, I.Shift k' -> k = k'
      | I.Dot (f_, s_), I.Dot (f'_, s'_) ->
          equalFront (f_, f'_) && equalSub (s_, s'_)
      | I.Dot (f_, s_), I.Shift k -> false
      | I.Shift k, I.Dot (f_, s_) -> false

    and equalFront = function
      | I.Idx n, I.Idx n' -> n = n'
      | I.Exp u_, I.Exp v_ -> Conv.conv ((u_, I.id), (v_, I.id))
      | I.Undef, I.Undef -> true

    let rec equalCtx' = function
      | I.Null, I.Null -> true
      | I.Decl (dk_, I.Dec (_, a_)), I.Decl (d1_, I.Dec (_, a1_)) ->
          Conv.conv ((a_, I.id), (a1_, I.id)) && equalCtx' (dk_, d1_)
      | I.Decl (dk_, I.ADec (_, d')), I.Decl (d1_, I.ADec (_, d)) ->
          d = d' && equalCtx' (dk_, d1_)
      | _, _ -> false

    let rec instanceCtx (asub, (d1_, g1_), (d2_, g2_)) =
      let d1 = I.ctxLength g1_ in
      let d2 = I.ctxLength g2_ in
      begin if d1 = d2 then
        try
          let fasub =
            assignCtx ((fun asub -> ()), (d1, 0), (d1_, g1_), (d2_, g2_))
          in
          begin
            fasub asub;
            true
          end
        with Assignment msg -> false
      else false
      end

    let rec collectEVar (d_, nsub) =
      let d'_ = emptyCtx () in
      let rec collectExp = function
        | d, d'_, d_, I.Lam (_, u_) -> collectExp (d + 1, d'_, d_, u_)
        | d, d'_, d_, I.Root (I.Const c, s_) -> collectSpine (d, d'_, d_, s_)
        | d, d'_, d_, I.Root (I.BVar k, s_) -> begin
            match member (k - d, d_) with
            | None -> collectSpine (d, d'_, d_, s_)
            | Some (x, dec_v) -> begin
                ignore (delete (x - d, d_));
                ignore (insertList ((x - d, dec_v), d'_))
              end
          end
        | d, d'_, d_, (I.Root (I.Def k, s_) as u_) ->
            let u'_ = Whnf.normalize (Whnf.expandDef (u_, I.id)) in
            collectExp (d, d'_, d_, u'_)
      and collectSpine = function
        | d, d'_, d_, I.Nil -> ()
        | d, d'_, d_, I.App (u_, s_) -> begin
            collectExp (d, d'_, d_, u_);
            collectSpine (d, d'_, d_, s_)
          end
      in
      begin
        S.forall nsub (function nv, (du, u_) -> collectExp (0, d'_, d_, u_));
        (d'_, d_)
      end

    let rec convAssSub' (g_, idx_k, d_, asub, d, ((evars, avars) as evarsl)) =
      begin match RBSet.lookup asub d with
      | None -> begin
          match member (d, d_) with
          | None -> IntSyn.Shift (evars + avars)
          | Some (x, IntSyn.Dec (n, v_)) ->
              let s = convAssSub' (g_, idx_k + 1, d_, asub, d + 1, evarsl) in
              let (I.EVar (r, _, _, cnstr) as e_) = I.newEVar (I.Null, v_) in
              I.Dot (I.Exp (I.EClo (e_, I.Shift (evars + avars))), s)
          | Some (x, IntSyn.ADec (n, v_)) -> begin
              print "convAssSub' -- Found an uninstantiated AVAR\n";
              raise (Error "Unassigned AVar -- should never happen\n")
            end
        end
      | Some (I.Exp e_ as f_) ->
          let e'_ = Whnf.normalize (e_, I.id) in
          I.Dot (I.Exp e'_, convAssSub' (g_, idx_k + 1, d_, asub, d + 1, evarsl))
      end

    let rec convAssSub (g_, asub, glength_, d'_, evarsl) =
      convAssSub' (g_, 0, d'_, asub, glength_, evarsl)

    let rec isExists (d, I.BVar k, d_) = member (k - d, d_)

    let rec instance ((d_t_, (dt, t_v)), (d_u_, (du, u_)), rho_u, ac) =
      let rec instRoot = function
        | ( depth,
            (I.Root ((I.Const k as h1_), s1_) as t_),
            (I.Root (I.Const k', s2_) as u_),
            ac ) -> begin
            if k = k' then instSpine (depth, s1_, s2_, ac)
            else raise (Instance "Constant mismatch\n")
          end
        | ( depth,
            (I.Root ((I.Def k as h1_), s1_) as t_),
            (I.Root (I.Def k', s2_) as u_),
            ac ) -> begin
            if k = k' then instSpine (depth, s1_, s2_, ac)
            else
              let t'_ = Whnf.normalize (Whnf.expandDef (t_v, I.id)) in
              let u'_ = Whnf.normalize (Whnf.expandDef (u_, I.id)) in
              instExp (depth, t'_, u'_, ac)
          end
        | ( depth,
            (I.Root ((I.Def k as h1_), s1_) as t_),
            (I.Root (h2_, s2_) as u_),
            ac ) ->
            let t'_ = Whnf.normalize (Whnf.expandDef (t_v, I.id)) in
            instExp (depth, t'_, u_, ac)
        | ( d,
            (I.Root ((I.BVar k as h1_), s1_) as t_),
            (I.Root (I.BVar k', s2_) as u_),
            ac ) -> begin
            if k > d && k' > d then
              let k1 = k - d in
              let k2 = k' - d in
              begin match (member (k1, d_t_), member (k2, d_u_)) with
              | None, None -> begin
                  if k1 = k2 then instSpine (d, s1_, s2_, ac)
                  else raise (Instance "Bound variable mismatch\n")
                end
              | Some (x, dec1_), Some (x', dec2_) -> begin
                  if k1 = k2 && equalDec (dec1_, dec2_) then
                    let ac' = instSpine (d, s1_, s2_, ac) in
                    let ac'' = function
                      | asub -> begin
                          ac' asub;
                          assign (d, dec1_, t_v, u_, asub)
                        end
                    in
                    ac''
                  else function
                    | asub -> begin
                        ac asub;
                        assign (d, dec1_, t_v, u_, asub)
                      end
                end
              | Some (x, (I.ADec (n, d') as dec1_)), None ->
                  fun asub ->
                    begin
                      ac asub;
                      assign (d, dec1_, t_v, u_, asub)
                    end
              | Some (x, dec1_), None ->
                  fun asub ->
                    begin
                      ac asub;
                      assign (d, dec1_, t_v, u_, asub)
                    end
              | _, _ -> raise (Instance "Impossible\n")
              end
            else raise (Instance "Bound variable mismatch\n")
          end
        | ( d,
            (I.Root ((I.BVar k as h1_), s1_) as t_),
            (I.Root (I.Const k', s2_) as u_),
            ac ) -> begin
            match isExists (d, I.BVar k, d_t_) with
            | None -> raise (Instance "Impossible\n")
            | Some (x, (I.ADec (_, _) as dec1_)) ->
                fun asub ->
                  begin
                    ac asub;
                    assign (d, dec1_, t_v, u_, asub)
                  end
            | Some (x, dec1_) ->
                fun asub ->
                  begin
                    ac asub;
                    assign (d, dec1_, t_v, u_, asub)
                  end
          end
        | ( d,
            (I.Root ((I.BVar k as h1_), s1_) as t_),
            (I.Root (I.Def k', s2_) as u_),
            ac ) -> begin
            match isExists (d, I.BVar k, d_t_) with
            | None -> raise (Instance "Impossible\n")
            | Some (x, (I.ADec (_, _) as dec1_)) ->
                fun asub ->
                  begin
                    ac asub;
                    assign (d, dec1_, t_v, u_, asub)
                  end
            | Some (x, dec1_) ->
                fun asub ->
                  begin
                    ac asub;
                    assign (d, dec1_, t_v, u_, asub)
                  end
          end
        | depth, (I.Root (h1_, s1_) as t_), (I.Root (I.Def k', s2_) as u_), ac
          ->
            let u'_ = Whnf.normalize (Whnf.expandDef (u_, I.id)) in
            instExp (depth, t_v, u'_, ac)
        | d, (I.Root (h1_, s1_) as t_), (I.Root (h2_, s2_) as u_), ac ->
            raise (Instance "Other Cases impossible\n")
      and instExp = function
        | d, (I.NVar n as t_), (I.Root (h_, s_) as u_), ac -> begin
            S.insert rho_u (n, (d, u_));
            ac
          end
        | d, (I.Root (h1_, s1_) as t_), (I.Root (h2_, s2_) as u_), ac ->
            instRoot (d, I.Root (h1_, s1_), I.Root (h2_, s2_), ac)
        | ( d,
            I.Lam ((I.Dec (_, a1_) as d1_), t1_),
            I.Lam ((I.Dec (_, a2_) as d2_), u2_),
            ac ) ->
            instExp (d + 1, t1_, u2_, ac)
        | d, t_v, u_, ac -> begin
            print "instExp -- falls through?\n";
            raise (Instance "Impossible\n")
          end
      and instSpine = function
        | d, I.Nil, I.Nil, ac -> ac
        | d, I.App (t_v, s1_), I.App (u_, s2_), ac ->
            let ac' = instExp (d, t_v, u_, ac) in
            let ac'' = instSpine (d, s1_, s2_, ac') in
            ac''
        | d, I.Nil, I.App (_, _), ac -> begin
            print
              "Spines are not the same -- (first one is Nil) -- cannot happen!\n";
            raise (Instance "DifferentSpines\n")
          end
        | d, I.App (_, _), I.Nil, ac -> begin
            print
              "Spines are not the same -- second one is Nil -- cannot happen!\n";
            raise (Instance "DifferentSpines\n")
          end
        | d, I.SClo (_, _), _, ac -> begin
            print "Spine Closure!(1) -- cannot happen!\n";
            raise (Instance "DifferentSpines\n")
          end
        | d, _, I.SClo (_, _), ac -> begin
            print "Spine Closure! (2) -- cannot happen!\n";
            raise (Instance " DifferentSpines\n")
          end
      in
      ac := instExp (dt, t_v, u_, !ac)

    let rec compHeads = function
      | (d_1_, I.Const k), (d_2_, I.Const k') -> k = k'
      | (d_1_, I.Def k), (d_2_, I.Def k') -> k = k'
      | (d_1_, I.BVar k), (d_2_, I.BVar k') -> begin
          match isExists (0, I.BVar k, d_1_) with
          | None -> k = k'
          | Some (x, dec_v) -> true
        end
      | (d_1_, I.BVar k), (d_2_, h2_) -> begin
          match isExists (0, I.BVar k, d_1_) with
          | None -> false
          | Some (x, dec_v) -> true
        end
      | (d_1_, h1_), (d_2_, h2_) -> false

    let rec compatible' ((d_t_, (dt, t_v)), (d_u_, (du, u_)), ds_, rho_t, rho_u)
        =
      let rec genNVar ((rho_t, t_v), (rho_u, u_)) =
        begin
          S.insert rho_t (!nctr + 1, t_v);
          begin
            S.insert rho_u (!nctr + 1, u_);
            newNVar ()
          end
        end
      in
      let rec genRoot = function
        | ( d,
            (I.Root ((I.Const k as h1_), s1_) as t_),
            (I.Root (I.Const k', s2_) as u_) ) -> begin
            if k = k' then
              let s'_ = genSpine (d, s1_, s2_) in
              I.Root (h1_, s'_)
            else genNVar ((rho_t, (d, t_v)), (rho_u, (d, u_)))
          end
        | ( d,
            (I.Root ((I.Def k as h1_), s1_) as t_),
            (I.Root (I.Def k', s2_) as u_) ) -> begin
            if k = k' then
              let s'_ = genSpine (d, s1_, s2_) in
              I.Root (h1_, s'_)
            else genNVar ((rho_t, (d, t_v)), (rho_u, (d, u_)))
          end
        | ( d,
            (I.Root ((I.BVar k as h1_), s1_) as t_),
            (I.Root (I.BVar k', s2_) as u_) ) -> begin
            if k > d && k' > d then
              let k1 = k - d in
              let k2 = k' - d in
              begin match (member (k1, d_t_), member (k2, d_u_)) with
              | None, None -> begin
                  if k1 = k2 then
                    try
                      let s'_ = genSpine (d, s1_, s2_) in
                      I.Root (h1_, s'_)
                    with differentSpine_ ->
                      genNVar ((rho_t, (d, t_v)), (rho_u, (d, u_)))
                  else genNVar ((rho_t, (d, t_v)), (rho_u, (d, u_)))
                end
              | Some (x, dec1_), Some (x', dec2_) -> begin
                  if k1 = k2 && equalDec (dec1_, dec2_) then
                    let s'_ = genSpine (d, s1_, s2_) in
                    begin
                      ignore (delete (x, d_t_));
                      begin
                        ignore (delete (x', d_u_));
                        begin
                          ignore (insertList ((x, dec1_), ds_));
                          I.Root (h1_, s'_)
                        end
                      end
                    end
                  else genNVar ((rho_t, (d, t_v)), (rho_u, (d, u_)))
                end
              | _, _ -> genNVar ((rho_t, (d, t_v)), (rho_u, (d, u_)))
              end
            else begin
              if k = k' then
                try
                  let s'_ = genSpine (d, s1_, s2_) in
                  I.Root (h1_, s'_)
                with DifferentSpines ->
                  genNVar ((rho_t, (d, t_v)), (rho_u, (d, u_)))
              else genNVar ((rho_t, (d, t_v)), (rho_u, (d, u_)))
            end
          end
        | ( d,
            (I.Root ((I.BVar k as h1_), s1_) as t_),
            (I.Root (I.Const k', s2_) as u_) ) ->
            genNVar ((rho_t, (d, t_v)), (rho_u, (d, u_)))
        | ( d,
            (I.Root ((I.BVar k as h1_), s1_) as t_),
            (I.Root (I.Def k', s2_) as u_) ) ->
            genNVar ((rho_t, (d, t_v)), (rho_u, (d, u_)))
        | d, (I.Root (h1_, s1_) as t_), (I.Root (h2_, s2_) as u_) ->
            genNVar ((rho_t, (d, t_v)), (rho_u, (d, u_)))
      and genExp = function
        | d, (I.NVar n as t_), (I.Root (h_, s_) as u_) -> begin
            S.insert rho_u (n, (d, u_));
            t_v
          end
        | d, (I.Root (h1_, s1_) as t_), (I.Root (h2_, s2_) as u_) ->
            genRoot (d, I.Root (h1_, s1_), I.Root (h2_, s2_))
        | ( d,
            I.Lam ((I.Dec (_, a1_) as d1_), t1_),
            I.Lam ((I.Dec (_, a2_) as d2_), u2_) ) ->
            let e_ = genExp (d + 1, t1_, u2_) in
            I.Lam (d1_, e_)
        | d, t_v, u_ -> begin
            print "genExp -- falls through?\n";
            genNVar ((rho_t, (d, t_v)), (rho_u, (d, u_)))
          end
      and genSpine = function
        | d, I.Nil, I.Nil -> I.Nil
        | d, I.App (t_v, s1_), I.App (u_, s2_) ->
            let e_ = genExp (d, t_v, u_) in
            let s'_ = genSpine (d, s1_, s2_) in
            I.App (e_, s'_)
        | d, I.Nil, I.App (_, _) -> raise DifferentSpines
        | d, I.App (_, _), I.Nil -> raise DifferentSpines
        | d, I.SClo (_, _), _ -> raise DifferentSpines
        | d, _, I.SClo (_, _) -> raise DifferentSpines
      in
      Variant (dt, genExp (dt, t_v, u_))

    let rec compatible = function
      | ( (d_t_, ((d1, I.Root (h1_, s1_)) as t_)),
          (d_u_, ((d2, I.Root (h2_, s2_)) as u_)),
          ds_,
          rho_t,
          rho_u ) -> begin
          if compHeads ((d_t_, h1_), (d_u_, h2_)) then
            compatible' ((d_t_, t_), (d_u_, u_), ds_, rho_t, rho_u)
          else NotCompatible
        end
      | (d_t_, t_v), (d_u_, u_), ds_, rho_t, rho_u ->
          compatible' ((d_t_, t_v), (d_u_, u_), ds_, rho_t, rho_u)

    let rec compatibleCtx = function
      | asub, (dsq_, gsq_, eqn_sq), [] -> None
      | ( asub,
          (dsq_, gsq_, eqn_sq),
          (_, delta'_, g'_, eqn', answRef', _, status') :: gRlist_ ) -> begin
          if instanceCtx (asub, (dsq_, gsq_), (delta'_, g'_)) then
            Some ((delta'_, g'_, eqn'), answRef', status')
          else compatibleCtx (asub, (dsq_, gsq_, eqn_sq), gRlist_)
        end

    let rec instanceSub ((d_t_, nsub_t), (dsq_, squery), asub) =
      let rho_u = nid () in
      let d_r2_ = copy dsq_ in
      let ac = ref (function (asub : exSubsts) -> ()) in
      try
        begin
          S.forall squery (function nv, (du, u_) ->
              begin match S.lookup nsub_t nv with
              | Some (dt, t_v) ->
                  instance ((d_t_, (dt, t_v)), (d_r2_, (du, u_)), rho_u, ac)
              | None -> S.insert rho_u (nv, (du, u_))
              end);
          begin
            ( ! ) ac asub;
            InstanceSub (asub, (d_r2_, rho_u))
          end
        end
      with Instance msg -> NoCompatibleSub

    let rec instChild = function
      | (Leaf ((d_t_, nsub_t), gList_) as n_), (d_sq_, sq), asub ->
          instanceSub ((d_t_, nsub_t), (d_sq_, sq), asub)
      | (Node ((d_t_, nsub_t), children'_) as n_), (d_sq_, sq), asub ->
          instanceSub ((d_t_, nsub_t), (d_sq_, sq), asub)

    let rec findAllInst (g_r_, children, ds_, asub) =
      let rec findAllCands = function
        | g_r_, [], (dsq_, sub_u), asub, iList_ -> iList_
        | g_r_, x :: l_, (dsq_, sub_u), asub, iList_ ->
            let asub' = S.copy asub in
            begin match instChild (!x, (dsq_, sub_u), asub) with
            | NoCompatibleSub ->
                findAllCands (g_r_, l_, (dsq_, sub_u), asub', iList_)
            | InstanceSub (asub, drho2_) ->
                findAllCands
                  (g_r_, l_, (dsq_, sub_u), asub', (x, drho2_, asub) :: iList_)
            end
      in
      findAllCands (g_r_, children, ds_, asub, [])

    let rec solveEqn = function
      | (trivial_, s), g_ -> true
      | (T.Unify (g'_, e1, n_, eqns), s), g_ ->
          let g''_ = compose (g'_, g_) in
          let s' = shift (g''_, s) in
          Assign.unifiable (g''_, (n_, s'), (e1, s')) && solveEqn ((eqns, s), g_)

    let rec solveEqn' = function
      | (trivial_, s), g_ -> true
      | (T.Unify (g'_, e1, n_, eqns), s), g_ ->
          let g''_ = compose (g'_, g_) in
          let s' = shift (g'_, s) in
          Assign.unifiable (g''_, (n_, s'), (e1, s'))
          && solveEqn' ((eqns, s), g_)

    let rec solveEqnI' = function
      | (trivial_, s), g_ -> true
      | (T.Unify (g'_, e1, n_, eqns), s), g_ ->
          let g''_ = compose (g'_, g_) in
          let s' = shift (g'_, s) in
          Assign.instance (g''_, (e1, s'), (n_, s'))
          && solveEqnI' ((eqns, s), g_)

    let rec retrieveInst (nref_, (dq_, sq), asub, gr_) =
      let rec retrieve' = function
        | ( (Leaf ((d_, s), gRlistRef_) as n_),
            (dq_, sq),
            asubst,
            ((((dEVars_, dAVars_) as dAEVars_), g_r_, eqn, stage, status) as
             gr'_) ) ->
            let dsq_, d_g_ = collectEVar (dq_, sq) in
            begin match
              compatibleCtx (asubst, (d_g_, g_r_, eqn), !gRlistRef_)
            with
            | None -> raise (Instance "Compatible path -- different ctx\n")
            | Some ((d'_, g'_, eqn'), answRef', status') ->
                let dAEVars_ = compose (dEVars_, dAVars_) in
                let esub = ctxToAVarSub (g'_, dAEVars_, I.Shift 0) in
                let asub =
                  convAssSub
                    ( g'_,
                      asubst,
                      I.ctxLength g'_ + 1,
                      d'_,
                      (I.ctxLength dAVars_, I.ctxLength dEVars_) )
                in
                let _ =
                  begin if solveEqn' ((eqn, shift (g'_, esub)), g'_) then ()
                  else print " failed to solve eqn_query\n"
                  end
                in
                let easub = normalizeSub (I.comp (asub, esub)) in
                begin if solveEqnI' ((eqn', shift (g'_, easub)), g'_) then
                  T.RepeatedEntry ((esub, asub), answRef', status')
                else
                  raise
                    (Instance "Compatible path -- resdidual equ. not solvable\n")
                end
            end
        | ( (Node ((d_, sub), children) as n_),
            (dq_, sq),
            asub,
            ((dAEVars_, g_r_, eqn, stage, status) as gr_) ) ->
            let instCand_ = findAllInst (g_r_, children, (dq_, sq), asub) in
            let rec checkCandidates = function
              | [] -> raise (Instance "No compatible child\n")
              | (childRef_, drho2_, asub) :: iCands_ -> (
                  try retrieve' (!childRef_, drho2_, asub, gr_)
                  with Instance msg -> checkCandidates iCands_)
            in
            checkCandidates instCand_
      in
      function () -> ((), retrieve' (!nref_, (dq_, sq), asub, gr_))

    let rec compatibleSub ((d_t_, nsub_t), (dsq_, squery)) =
      let sigma, rho_t, rho_u = (nid (), nid (), nid ()) in
      let dsigma_ = emptyCtx () in
      let d_r1_ = copy d_t_ in
      let d_r2_ = copy dsq_ in
      let choose = ref (function (match_ : bool) -> ()) in
      let _ =
        S.forall squery (function nv, u_ ->
            begin match S.lookup nsub_t nv with
            | Some t_v -> begin
                match
                  compatible ((d_r1_, t_v), (d_r2_, u_), dsigma_, rho_t, rho_u)
                with
                | NotCompatible -> begin
                    S.insert rho_t (nv, t_v);
                    S.insert rho_u (nv, u_)
                  end
                | Variant (dt_, t'_) ->
                    let restc = !choose in
                    begin
                      S.insert sigma (nv, (dt_, t'_));
                      choose :=
                        function
                        | match_ -> begin
                            restc match_;
                            begin if match_ then () else ()
                            end
                          end
                    end
              end
            | None -> S.insert rho_u (nv, u_)
            end)
      in
      begin if isId rho_t then begin
        ( ! ) choose true;
        VariantSub (d_r2_, rho_u)
      end
      else begin
        ( ! ) choose false;
        begin if isId sigma then NoCompatibleSub
        else SplitSub ((dsigma_, sigma), (d_r1_, rho_t), (d_r2_, rho_u))
        end
      end
      end

    let rec mkNode = function
      | ( Node (_, children_),
          ((ds_, sigma) as dsigma_),
          ((d1_, rho1) as drho1_),
          (((evarl, l), dp, eqn, answRef, stage, status) as gr_),
          ((d2_, rho2) as drho2_) ) ->
          let d_rho2_, d_g2_ = collectEVar (d2_, rho2) in
          let gr'_ = ((evarl, l), d_g2_, dp, eqn, answRef, stage, status) in
          let sizeSigma, sizeRho1, sizeRho2 =
            (S.size sigma, S.size rho1, S.size rho2)
          in
          Node
            ( dsigma_,
              [
                ref (Leaf ((d_rho2_, rho2), ref [ gr'_ ]));
                ref (Node (drho1_, children_));
              ] )
      | ( Leaf (c, gRlist_),
          ((ds_, sigma) as dsigma_),
          ((d1_, rho1) as drho1_),
          (((evarl, l), dp, eqn, answRef, stage, status) as gr2_),
          ((d2_, rho2) as drho2_) ) ->
          let d_rho2_, d_g2_ = collectEVar (d2_, rho2) in
          let gr2'_ = ((evarl, l), d_g2_, dp, eqn, answRef, stage, status) in
          Node
            ( dsigma_,
              [
                ref (Leaf ((d_rho2_, rho2), ref [ gr2'_ ]));
                ref (Leaf (drho1_, gRlist_));
              ] )

    let rec compChild = function
      | (Leaf ((d_t_, nsub_t), gList_) as n_), (d_e_, nsub_e) ->
          compatibleSub ((d_t_, nsub_t), (d_e_, nsub_e))
      | (Node ((d_t_, nsub_t), children'_) as n_), (d_e_, nsub_e) ->
          compatibleSub ((d_t_, nsub_t), (d_e_, nsub_e))

    let rec findAllCandidates (g_r_, children, ds_) =
      let rec findAllCands = function
        | g_r_, [], (dsq_, sub_u), vList_, sList_ -> (vList_, sList_)
        | g_r_, x :: l_, (dsq_, sub_u), vList_, sList_ -> begin
            match compChild (!x, (dsq_, sub_u)) with
            | NoCompatibleSub ->
                findAllCands (g_r_, l_, (dsq_, sub_u), vList_, sList_)
            | SplitSub (dsigma_, drho1_, drho2_) ->
                findAllCands
                  ( g_r_,
                    l_,
                    (dsq_, sub_u),
                    vList_,
                    (x, (dsigma_, drho1_, drho2_)) :: sList_ )
            | VariantSub (d_r2_, rho2) ->
                let drho2_ = (d_r2_, rho2) in
                findAllCands
                  (g_r_, l_, (dsq_, sub_u), (x, drho2_, I.id) :: vList_, sList_)
          end
      in
      findAllCands (g_r_, children, ds_, [], [])

    let rec divergingCtx (stage, g_, gRlistRef_) =
      let l = I.ctxLength g_ + 3 in
      List.exists
        (function
          | (_, l), d_, g'_, _, _, stage', _ ->
              stage = stage' && l > I.ctxLength g'_)
        !gRlistRef_

    let rec eqHeads = function
      | I.Const k, I.Const k' -> k = k'
      | I.BVar k, I.BVar k' -> k = k'
      | I.Def k, I.Def k' -> k = k'
      | _, _ -> false

    let rec eqTerm = function
      | I.Root (h2_, s2_), ((I.Root (h_, s_) as t), rho1) -> begin
          eqHeads (h2_, h_) && eqSpine (s2_, (s_, rho1))
        end
      | t2_, (I.NVar n, rho1) -> begin
          match S.lookup rho1 n with
          | None -> false
          | Some (dt1, t1_) -> eqTerm (t2_, (t1_, nid ()))
        end
      | I.Lam (d2_, t2_), (I.Lam (d_, t_v), rho1) -> eqTerm (t2_, (t_v, rho1))
      | _, (_, _) -> false

    and eqSpine = function
      | I.Nil, (I.Nil, rho1) -> true
      | I.App (t2_, s2_), (I.App (t_v, s_), rho1) ->
          eqTerm (t2_, (t_v, rho1)) && eqSpine (s2_, (s_, rho1))

    let rec divergingSub ((ds_, sigma), (dr1_, rho1), (dr2_, rho2)) =
      S.exists rho2 (function n2, (dt2, t2) ->
          S.exists sigma (function _, (d, t) -> eqTerm (t2, (t, rho1))))

    let rec variantCtx = function
      | (g_, eqn), [] -> None
      | (g_, eqn), (l', d_g_, g'_, eqn', answRef', _, status') :: gRlist_ ->
        begin
          if equalCtx' (g_, g'_) && equalEqn (eqn, eqn') then
            Some (l', answRef', status')
          else variantCtx ((g_, eqn), gRlist_)
        end

    let rec insert (nref_, (dsq_, sq), gr_) =
      let rec insert' = function
        | ( (Leaf (_, gRlistRef_) as n_),
            (dsq_, sq),
            ((l, g_r_, eqn, answRef, stage, status) as gr_) ) -> begin
            match variantCtx ((g_r_, eqn), !gRlistRef_) with
            | None -> (
                let d_nsub_, d_g_ = collectEVar (dsq_, sq) in
                let gr'_ = (l, d_g_, g_r_, eqn, answRef, stage, status) in
                function
                | () ->
                    ( begin
                        gRlistRef_ := gr'_ :: !gRlistRef_;
                        answList := answRef :: !answList
                      end,
                      T.NewEntry answRef ))
            | Some (_, answRef', status') -> (
                function
                | () -> ((), T.RepeatedEntry ((I.id, I.id), answRef', status')))
          end
        | ( (Node ((d_, sub), children) as n_),
            (dsq_, sq),
            ((l, g_r_, eqn, answRef, stage, status) as gr_) ) ->
            let variantCand_, splitCand_ =
              findAllCandidates (g_r_, children, (dsq_, sq))
            in
            let d_nsub_, d_g_ = collectEVar (dsq_, sq) in
            let gr'_ = (l, d_g_, g_r_, eqn, answRef, stage, status) in
            let rec checkCandidates = function
              | [], [] -> (
                  function
                  | () ->
                      ( begin
                          nref_ :=
                            Node
                              ( (d_, sub),
                                ref (Leaf ((d_nsub_, sq), ref [ gr'_ ]))
                                :: children );
                          answList := answRef :: !answList
                        end,
                        T.NewEntry answRef ))
              | [], (childRef_, (dsigma_, drho1_, drho2_)) :: _ -> begin
                  if
                    !TableParam.divHeuristic
                    && divergingSub (dsigma_, drho1_, drho2_)
                  then function
                    | () ->
                        ( begin
                            childRef_ :=
                              mkNode (!childRef_, dsigma_, drho1_, gr_, drho2_);
                            answList := answRef :: !answList
                          end,
                          T.DivergingEntry (I.id, answRef) )
                  else function
                    | () ->
                        ( begin
                            childRef_ :=
                              mkNode (!childRef_, dsigma_, drho1_, gr_, drho2_);
                            answList := answRef :: !answList
                          end,
                          T.NewEntry answRef )
                end
              | (childRef_, drho2_, asub) :: [], _ ->
                  insert (childRef_, drho2_, gr_)
              | (childRef_, drho2_, asub) :: l_, sCands_ -> begin
                  match (insert (childRef_, drho2_, gr_)) () with
                  | _, T.NewEntry answRef -> checkCandidates (l_, sCands_)
                  | _, T.RepeatedEntry (asub, answRef, status) ->
                      fun () -> ((), T.RepeatedEntry (asub, answRef, status))
                  | _, T.DivergingEntry (asub, answRef) ->
                      fun () -> ((), T.DivergingEntry (asub, answRef))
                end
            in
            checkCandidates (variantCand_, splitCand_)
      in
      insert' (!nref_, (dsq_, sq), gr_)

    let rec answCheckVariant (s', answRef, o_) =
      let rec member = function
        | (d_, sk), [] -> false
        | (d_, sk), ((d1_, s1), _) :: s_ -> begin
            if equalSub (sk, s1) && equalCtx' (d_, d1_) then true
            else member ((d_, sk), s_)
          end
      in
      let dEVars_, sk = A.abstractAnswSub s' in
      begin if member ((dEVars_, sk), T.solutions answRef) then T.Repeated_
      else begin
        T.addSolution (((dEVars_, sk), o_), answRef);
        T.New_
      end
      end

    let rec reset () =
      begin
        nctr := 1;
        Array.modify
          (function
            | n, tree -> begin
                n := 0;
                begin
                  tree := !(makeTree ());
                  begin
                    answList := [];
                    begin
                      added := false;
                      (n, tree)
                    end
                  end
                end
              end)
          indexArray
      end

    let rec makeCtx = function
      | n, I.Null, (dEVars_ : ctx) -> ()
      | n, I.Decl (g_, d_), (dEVars_ : ctx) -> begin
          insertList ((n, d_), dEVars_);
          makeCtx (n + 1, g_, dEVars_)
        end

    let rec callCheck (a, dAVars_, dEVars_, g_, u_, eqn, status) =
      let n, tree = Array.sub (indexArray, a) in
      let sq = S.new_ () in
      let dAEVars_ = compose (dEVars_, dAVars_) in
      let dq_ = emptyCtx () in
      let n = I.ctxLength g_ in
      let _ = makeCtx (n + 1, dAEVars_, (dq_ : ctx)) in
      let l = I.ctxLength dAEVars_ in
      let _ = S.insert sq (1, (0, u_)) in
      let gr_ =
        ((l, n + 1), g_, eqn, emptyAnswer (), !TableParam.stageCtr, status)
      in
      let gr'_ = ((dEVars_, dAVars_), g_, eqn, !TableParam.stageCtr, status) in
      let result =
        try retrieveInst (tree, (dq_, sq), asid (), gr'_)
        with Instance msg -> insert (tree, (dq_, sq), gr_)
      in
      begin match result () with
      | _, T.NewEntry answRef -> begin
          begin
            added := true;
            T.NewEntry answRef
          end
        end
      | _, T.RepeatedEntry (asub, answRef, status) ->
          T.RepeatedEntry (asub, answRef, status)
      | _, T.DivergingEntry (asub, answRef) -> begin
          begin
            added := true;
            T.DivergingEntry (asub, answRef)
          end
        end
      end

    let rec insertIntoTree (a, dAVars_, dEVars_, g_, u_, eqn, answRef, status) =
      let n, tree = Array.sub (indexArray, a) in
      let sq = S.new_ () in
      let dAEVars_ = compose (dEVars_, dAVars_) in
      let dq_ = emptyCtx () in
      let n = I.ctxLength g_ in
      let _ = makeCtx (n + 1, dAEVars_, (dq_ : ctx)) in
      let l = I.ctxLength dAEVars_ in
      let _ = S.insert sq (1, (0, u_)) in
      let gr_ =
        ((l, n + 1), g_, eqn, emptyAnswer (), !TableParam.stageCtr, status)
      in
      let result =
        insert
          ( tree,
            (dq_, sq),
            ((l, n + 1), g_, eqn, answRef, !TableParam.stageCtr, status) )
      in
      begin match result () with
      | _, T.NewEntry answRef -> begin
          begin
            added := true;
            T.NewEntry answRef
          end
        end
      | _, T.RepeatedEntry (asub, answRef, status) ->
          T.RepeatedEntry (asub, answRef, status)
      | _, T.DivergingEntry (asub, answRef) -> begin
          begin
            added := true;
            T.DivergingEntry (asub, answRef)
          end
        end
      end

    let rec answCheck (s', answRef, o_) = answCheckVariant (s', answRef, o_)

    let rec updateTable () =
      let rec update arg__1 arg__2 =
        begin match (arg__1, arg__2) with
        | [], flag_ -> flag_
        | answRef :: aList_, flag_ ->
            let l = length (T.solutions answRef) in
            begin if l = T.lookup answRef then update aList_ flag_
            else begin
              T.updateAnswLookup (l, answRef);
              update aList_ true
            end
            end
        end
      in
      let flag_ = update !answList false in
      let r = flag_ || !added in
      begin
        added := false;
        r
      end
  end

  (* index for normal variables *)
  (* index for bound variables *)
  (* depth of locally bound variables *)
  (* ------------------------------------------------------ *)
  (* for debugging only *)
  (* auxiliary function  -- needed to dereference AVars -- expensive?*)
  (* ------------------------------------------------------ *)
  (* Auxiliary functions *)
  (* etaSpine (S, n) = true

   iff S is a spine n;n-1;..;1;nil

   no permutations or eta-expansion of arguments are allowed
   *)
  (* compose (Decl(G',D1'), G) =   G. .... D3'. D2'.D1'
       where G' = Dn'....D3'.D2'.D1' *)
  (* ---------------------------------------------------------------------- *)
  (* ctxToEVarSub D = s

     if D is a context for existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)
  (* ---------------------------------------------------------------------- *)
  (* Matching for linear terms based on assignment *)
  (* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)
  (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)
  (* lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) = *)
  (* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *)
  (* It is not clear if this case can happen *)
  (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
  (* assign(d, Dec(n, V), X as I.Root(BVar k, S), U, asub) = ()
      Invariant:
      if D ; G |- U : V
         D ; G |- X : V
      then
         add (X, U) to asub
         where  assub is a set of substitutions for existential variables)
    *)
  (* [asub]E1  = U *)
  (* total as (t, passed)*)
  (* it is an evar -- (k-d, EVar (SOME(U), V)) *)
  (* total as (t, passed)*)
  (* it is an Avar and d = d' (k-d, AVar(SOME(U)) *)
  (* terms are in normal form *)
  (* exception Assignment of string *)
  (* assignExp (fasub, (l, ctxTotal as (r, passed), d) (D1, U1), (D2, U2))) = fasub'

     invariant:
      G, G0 |- U1 : V1   U1 in nf
      G, G0 |- U2 : V2   U2 in nf
     and U1, U2 are linear higher-order patterns
      D1 contains all existential variables of U1
      D2 contains all existential variables of U2

      ctxTotal = (r + passed) = |G|
            where G refers to the globally bound variables
      d = |G0| where G' refers to the locally bound variables

      then fasub' is a success continuation
        which builds up a substitution s
              with domain D1 and  U1[s] = U2

      NOTE: We only allow assignment for fully applied evars --
      and we will fail otherwise. This essentially only allows first-order assignment.
      To generalize this, we would need to linearize the ctx and have more complex
      abstraction algorithm.

   *)
  (* we do not expand definitions here -- this is very conservative! *)
  (* we do not expand definitions here -- this is very conservative! *)
  (* we do not expand definitions here -- this is very conservative! *)
  (* if (k1 - d) >= l *)
  (* k1 is a globally bound variable *)
  (* k2 is globally bound *)
  (* k1 is an existial variable *)
  (* k2 is globally bound *)
  (* denote the same evar *)
  (* ctxTotal,*)
  (* can this happen ? -- definitions should be already expanded ?*)
  (* type labels are ignored *)
  (* is this necessary? Tue Aug  3 11:56:17 2004 -bp *)
  (* the closure cases should be unnecessary, if everything is in nf *)
  (* assignCtx (fasub, ctxTotal as (r, passed), (D1, G), (D2, G')) = fasub'
      invariant
         |G| = |G'| = r
         |G0| = |G0'| = passed
         |G, G0| = |G', G0'| = (r + passed) = ctxTotal

         D1 contains all existential variables occuring in (G, G0)
         D2 contains all existential variables occuring in (G', G0')

         fasub' is a success continuation
            which builds up a substitution s
              with domain D1 and  (G, G0)[s] = (G, G0)

         NOTE : [fasub]G = G' Sun Nov 28 18:55:21 2004 -bp
    *)
  (* ------------------------------------------------------ *)
  (*  Variable b    : bound variable
    Variable n    : index variable
    linear term  U ::=  Root(c, S) | Lam (D, U) | Root(b, S)
    linear Spine S ::= p ; S | NIL
    indexed term t ::= Root(n, NIL) |  Root(c, S) | Lam (D, p) | Root(b, S)
    indexed spines S_i ::= t ; S_i | NIL
    Types   A
    Context G : context for bound variables (bvars)
    (type information is stored in the context)

       G ::= . | G, x : A
       Set of all index variables:  N

    linear terms are well-typed in G:     G |- p
    indexed terms are well-typed in (N ; G) |- t

    Let s is a substitution for index variables (nvar)
    and s1 o s2 o .... o sn = s, s.t.
    forall nvar in CODOM(sk).
     exists i . nvar in DOM(si) and i > k.

    IMAGE (s) = the index variables occurring in the CODOM(s)

    Let N1 ... Nn be the path from the root N1 to the leaf Nn,
    and si the substitution associated with node Ni.

    IMAGE(sn) = empty
    s1 o s2 o ... o sn = s and IMAGE(s) = empty
    i.e. index variables are only internally used and no
         index variable is left.

    A linear term U (and an indexed term t) can be decomposed into a term t' together with
    a sequenence of substitutions s1, s2, ..., sn such that s1 o s2 o .... o sn = s
    and the following holds:

    If    N  ; G |- t
    then  N' ; G |- t'
          N  ; G |- s : N' ; G
          N  ; G |- t'[s]     and t'[s] = t

   if we have a linear term then N will be empty, but the same holds.

   In addition:
   all expressions in the index are closed and linear and in normalform i.e.
   an expression is first linearized before it is inserted into the index

   *)
  (* ---------------------------------------------------------------*)
  (* nctr = |D| =  #index variables *)
  (* too restrictive if we require order of both eqn must be the same ?
     Sun Sep  8 20:37:48 2002 -bp *)
  (* s = s' = I.id *)
  (* equalEqn (e, e') = (e = e') *)
  (* equalEqn' (d, (D, e), (D', e'), asub) = (e = e')

       destructively updates asub such that all the evars occurring in D'
       will be instantiated and  D |- asub : D'

       if D |- e and D' |- e'  and d = depth of context G'
          asub partially instantiates variables from D'
       then
         D |- asub : D'

    *)
  (* AVar *)
  (* AVar *)
  (* X is the evar in the query, X' is the evar in the index,
             potentially X' is not yet instantiated and X' in D' but X' not in asub *)
  (* k refers to an evar *)
  (* it is not instantiated yet *)
  (* it is instantiated;
                                          since eqn were solvable, eqn' would be solvable too *)
  (* k refers to a bound variable *)
  (* equalSub (s, s') = (s=s') *)
  (* equalFront (F, F') = (F=F') *)
  (* equalCtx' (G, G') = (G=G') *)
  (* ---------------------------------------------------------------*)
  (* destructively may update asub ! *)
  (* print msg;*)
  (* ---------------------------------------------------------------*)
  (* collect EVars in sub *)
  (* collectEVar (D, sq) = (D_sub, D')
     if D |- sq where D is a set of free variables
     then Dsq |- sq  and (Dsq u D') = D
          Dsq contains all the free variables occuring in sq
          D' contains all the free variables corresponding to Gsq
   *)
  (* ---------------------------------------------------------------*)
  (* most specific linear common generalization *)
  (* compatible (t_v, U) = (t_v', rho_u, rho_t) opt
    if t_v is an indexed term
       U is a linear term
       U and t_v share at least the top function symbol
   then
       t_v'[rho_u] = U and t_v'[rho_t] = t_v
   *)
  (* 0 *)
  (* Found an EVar which is not yet
                     instantiated -- must be instantiated when
                     solving residual equations! *)
  (* should never happen -- all avars should
                     have been assigned! *)
  (* [s']t_v = U so U = query and t_v is in the index *)
  (* globally bound variable *)
  (* both refer to the same globally bound variable in G *)
  (* k, k' refer to the existential *)
  (* they refer to the same existential variable *)
  (* this is unecessary *)
  (* since existential variables have the same type
                             and need to be fully applied in order, S1 = S2 *)
  (* S.insert asub (k - d, I.Idx (k-d)) *)
  (* ctxTotal,*)
  (* instance checking only Sun Oct 27 12:16:10 2002 -bp *)
  (* ctxTotal,*)
  (* instance checking only Sun Oct 27 12:18:53 2002 -bp *)
  (* ctxTotal,*)
  (* ctxTotal,*)
  (* locally bound variables *)
  (* this case only should happen during instance checking *)
  (* ctxTotal,*)
  (* ctxTotal, *)
  (* this case only should happen during instance checking *)
  (* ctxTotal,*)
  (* ctxTotal, *)
  (* by invariant A1 = A2 -- actually this invariant may be violated, but we ignore it. *)
  (* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
  (* by invariant dt = du *)
  (* if it succeeds then it will return a continuation which will
         instantiate the ""evars"" and rho_t will contain all
         nvar instantiations
         otherwise it will raise Instance *)
  (* by invariant dt = du *)
  (* could expand definitions here ? -bp*)
  (* globally bound variable *)
  (* should never happen *)
  (* k, k' refer to the existential *)
  (* they refer to the same existential variable *)
  (* this is unecessary -- since existential variables have the same type
                            and need to be fully applied in order, S1 = S2 *)
  (* variant checking only *)
  (* locally bound variables *)
  (* by invariant A1 = A2 *)
  (* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
  (* by invariant dt = du *)
  (* compatibleCtx (asub, (Dsq, Gsq, eqn_sq), GR) = option

    if Dsq is a subset of Dsq_complete
       where Dsq_complete encompasses all evars and avars in the original query
       Dsq |- Gsq ctx
       Dsq, Gsq |- eqn_sq
       there exists (_, D', G', eqn', ansRef', _, status') in GR
       s.t.
       Gsq is an instance of G'
       (andalso eqn_sq = eqn')
    then
      SOME((D', G', eqn'), answRef', status)
      and asub is destructively updated s.t. Dsq_complete |- Gsq = [asub]G'

    else
      NONE
   *)
  (* ---------------------------------------------------------------*)
  (* instanceSub(nsub_t, squery) = (rho_u, asub)

   if DOM(nsub_t) <= DOM(nsub_u)
      CODOM(nsub_t) : index terms
      CODOM(nsub_u) : linear terms
        G_u, Glocal_u |- nsub_u
    N ; G_t, Glocal_t |- nsub_t
   then
     nsub_t = sigma o rho_t
     nsub_e = sigma o rho_u

    Glocal_e ~ Glocal_t  (have ""approximately"" the same type)
    l_g = |Glocal_u|


    [asub]nsub_t = squery
   *)
  (* by invariant rho_t = empty, since nsub_t <= squery *)
  (* note by invariant Glocal_e ~ Glocal_t *)
  (* [ac]t_v = U *)
  (* if U is an instance of t_v then [ac][rc_u]t_v = U *)
  (* once the continuations ac are triggered *)
  (* [asub]nsub_t = sq  where sq is the query substitution *)
  (* will update asub *)
  (* Solving  variable definitions *)
  (* solveEqn ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
  (* evar *)
  (* Mon Dec 27 11:57:35 2004 -bp *)
  (* solveEqn' ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
  (* evar *)
  (* Mon Dec 27 12:20:45 2004 -bp
  solveEqn' ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 
  fun solveEqn' (T.Trivial, s) = true
    | solveEqn' (T.Unify(G',e1, N  evar , eqns), s) =
      let
        val s' = shift (G', s)
      in
        Assign.unifiable (G', (N, s'),(e1, s'))
        andalso solveEqn' (eqns, s)
     end

  solveEqnI' ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 
  fun solveEqnI' (T.Trivial, s) = true
    | solveEqnI' (T.Unify(G',e1, N  evar , eqns), s) =
      let
        val s' = shift (G', s)
         note: we check whether N[s'] is an instance of e1[s'] !!! 
         at this point all AVars have been instantiated, and we could use Match.instance directly 
      in
        Assign.instance (G', (e1, s'), (N, s'))
        andalso solveEqnI' (eqns, s)
     end
 Mon Dec 27 11:58:21 2004 -bp *)
  (* solveEqnI' ((VarDef, s), G) = bool

    if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
  (* evar *)
  (* note: we check whether N[s'] is an instance of e1[s'] !!! *)
  (* at this point all AVars have been instantiated, and we could use Match.instance directly *)
  (* retrieve all Instances from substitution tree *)
  (* retreiveInst (Nref, (Dq, sq), s', GR) = callCheckResult

      Invariant:

      If there exists a path r1 ... rn = p
         in the substitution tree with root Nref
         and there exists an assignable substitution s' (D
         s.t. [r']
      then
         return RepeatedEntry
      else raises exception instance
    *)
  (* s and sq are compatible by invariant *)
  (* [asub]s = sq   and there exists a path (D1, s1) ... (Dn,sn) from the root to the leaf (D,s)
           s.t. [asub]s1 o s2 o ... sn o s corresponds to original query
           *)
  (* Dq = (Dsq' u Dg) where Dsq' = evars occurring in sq
                                      D_G = evars occuring in G_sq or only in eqn_sq

               and Dsq = D since there exists a path s1 ... sn from the root to the leaf (D,s)
                 s.t. [asub]s1 o s2 o ... sn o s corresponds to original query
             *)
  (* compatibleCtx may destructively update asub ! *)
  (* compatible path -- but different ctx *)
  (* compatible path -- SAME ctx *)
  (* note: previously we checked eqn' = eqn! -- this is too restrictive
                 now - Dec  6 2004 -bp we check whether eqn is an instance of eqn'
                 note: this is very delicate code.
               *)
  (* Since there exists a path (D1, s1) ... (Dn,sn) from the root to the leaf (D,s)
                   D1', ...., Dn', D, D' = D*
                   and          G' |- esub' : DAEVars, G'        and       .   |- esub : DAEVars
                        DAEVars, G |- asub' : D*, G'                   DAEVars |- asub : D*

                  note: asub' may refer to free variables which denote evars in D*
                        which only occur in eqn' and hence have not yet been instantiated
                        however: all avars in D* have been instantiated!
                 *)
  (* Residual equation of query:
                   DAEVars, G' |- eqn  hence we solve : G' |= [esub']eqn *)
  (* = G_r *)
  (*              val _ = if solveEqn' (eqn, esub)
                          then () else print "" failed to solve eqn_query\n""  *)
  (* Residual equations in index:
                   D*, G' |- eqn'    where eqn' = AVar1 = E1 .... AVarn = En
                                      and  Ei may contain free variables
                      G'  |= [esub](asub) (eqn')

                      solve eqn' from path in index using instance or matching ONLY
                      to instantiate the free variables Ei

                   remark: DAEVars, G' |= [asub]eqn'   should work in theory too,
                           if the free variables in asub are created in such a way that they may depend on DAVars.
                           otherwise unification or instance checking will fail or the resulting instantiation
                           for the free variables in asub is too restrictive, s.t. retrieval fails
                   *)
  (*              if solveEqnI' (eqn', easub) *)
  (* solve residual equations using higher-order matching Wed Dec 22 2004 -bp *)
  (* no child is compatible with sq *)
  (* there is an instance  *)
  (* print msg; *)
  (*---------------------------------------------------------------------------*)
  (* insert new entry into substitution tree *)
  (* assuming there is no compatible entry already *)
  (* compatibleSub(nsub_t, squery) = (sigma, rho_t, rho_u) opt

   if DOM(nsub_t) <= DOM(squery)
      CODOM(nsub_t) : index terms
      CODOM(squery) : linear terms
        G_u, Glocal_u |- squery
    N ; G_t, Glocal_t |- nsub_t
   then
     nsub_t = sigma o rho_t
     nsub_e = sigma o rho_u

    Glocal_e ~ Glocal_t  (have ""approximately"" the same type)

   *)
  (* by invariant rho_t = empty, since nsub_t <= squery *)
  (* note by invariant Glocal_e ~ Glocal_t *)
  (* here Glocal_t will be only approximately correct! *)
  (* perfect match under asub and rho_t = nsub_t
           sigma = rho_t and sigma o asub = rho_u *)
  (* split -- asub is unchanged *)
  (* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *)
  (* ---------------------------------------------------------------------- *)
  (*  fun mkLeaf (Ds, GR, n) = Leaf (Ds, GR)*)
  (* ---------------------------------------------------------------------- *)
  (* ---------------------------------------------------------------------- *)
  (* this 3 is arbitrary -- lockstep *)
  (* eqTerm (t2, (t, rho1)) = bool
    returns true iff t2 = t[rho1]
  t2 is a linear term which may not contain any nvars!
  t may contain nvars
 *)
  (* ---------------------------------------------------------------------- *)
  (* Insert via variant checking *)
  (* insert (Nref, (Dq, sq), GR) = TableResult *)
  (* compatible path -- but different ctx! *)
  (* D_G contains evars occurring only in eqn or G
                        D_nsub contains evars occurring only in sq
                        furthermore: D_nsub = D where Leaf((D,s), GRlistRef)
                     *)
  (* compatible path -- SAME ctx and SAME eqn!
                                          this implies: SAME D_G *)
  (* no child is compatible with sq *)
  (* split an existing node *)
  (* substree diverging -- splitting node *)
  (* split existing node *)
  (* unique ""perfect"" candidate (left) *)
  (* there are several ""perfect"" candidates *)
  (* ---------------------------------------------------------------------- *)
  (* answer check and insert

     Invariant:
        D |- Pi G.U
          |- (Pi G.U)[s]
       .  |- s : D
       {{K}} are all the free variables in s
        D_k is the linear context of all free variables in {{K}}
        D_k |- s_k : D  and eqn
        D_k |- (Pi G.U)[s_k] and eqn

      answerCheck (G, s, answRef, 0) = repeated
         if (D_k, s_k, eqn)  already occurs in answRef
      answerCheck (G,s, answRef, O) = new
         if (D_k, s_k, eqn) did not occur in answRef
         Sideeffect: update answer list for U
     *)
  (* ---------------------------------------------------------------------- *)
  (* Reset Subsitution Tree *)
  (* makeCtx (n, G, G') =  unit
     if G LF ctx
     then
      G' is a set
      where (i,Di) corresponds to the i-th declaration in G

    note: G' is destructively updated
    *)
  (* callCheck (a, DAVars, DEVars, G, U, eqn, status) = TableResult
    if
      U is atomic (or base type) i.e. U = a S

      DAVars, DEVars, G |- U
      DAVars, DEVars, G |- eqn

      Tree is the substitution trie associated with type family a

   then
      if there exists a path r1 o r2 o ... o rn = p in Tree
         together with some (G',eqn', answRef') at the leaf
         and DAVars', DEVars', G' |- p
      and there exists a substitution s' s.t.

          DAVars, DEVars |- s' : DAVars', DEVars'
          [s']G' = G and [s']p = U

      and moreover
          there exists a substitution r' s.t.  G |- r' : DAVars, DEVars, G
          (which re-instantiates evars)

      and
            G |= [r']eqn    and [s']G' |= [r'][s']eqn'
     then
       TableResult = RepeatedEntry(s', answRef')

     otherwise

       TableResult = NewEntry (answRef')
       and there exists a path r1 o r2 o ... o rk = U in Tree
           together with (G,eqn, answRef) at the leaf

   *)
  (* n = |G| *)
  (* Dq = DAVars, DEVars *)
  (* l = |D| *)
  (* assignable subst *)
  (* sq not in index --> insert it *)
  (* we assume we alsways insert new things into the tree *)
  (* sq = query substitution *)
  (* no new solutions were added in the previous stage *)
  (* new solutions were added *)
  let reset = reset

  let callCheck = function
    | dAVars_, dEVars_, g_, u_, eqn, status ->
        callCheck
          (cidFromHead (I.targetHead u_), dAVars_, dEVars_, g_, u_, eqn, status)

  let insertIntoTree = function
    | dAVars_, dEVars_, g_, u_, eqn, answRef, status ->
        insertIntoTree
          ( cidFromHead (I.targetHead u_),
            dAVars_,
            dEVars_,
            g_,
            u_,
            eqn,
            answRef,
            status )

  let answerCheck = answCheck
  let updateTable = updateTable
  let tableSize () = length !answList

  (* memberCtxS ((G,V), G', n) = bool

       if G |- V and |- G' ctx
          exists a V' in G s.t.  V'[^n]  is an instance of V
       then return true
         otherwise false
    *)
  let rec memberCtx ((g_, v_), g'_) =
    let rec instanceCtx' = function
      | (g_, v_), I.Null, n -> None
      | (g_, v_), I.Decl (g'_, (I.Dec (_, v'_) as d'_)), n -> begin
          if Match.instance (g_, (v_, I.id), (v'_, I.Shift n)) then Some d'_
          else instanceCtx' ((g_, v_), g'_, n + 1)
        end
    in
    instanceCtx' ((g_, v_), g'_, 1)
end
(*! sharing Print.IntSyn = IntSyn'!*)
(* local *)
(* functor MemoTable *)

(* # 1 "src/opsem/subtree_inst.sml.ml" *)
