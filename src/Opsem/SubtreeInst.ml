open! Global.Global_
open! Table
open! Intsyn.Lambda_
open! Print.Print_
open! Compile
open! CompSyn
open! Assign

(* # 1 "src/opsem/SubtreeInst.sig.ml" *)

(* # 1 "src/opsem/SubtreeInst.fun.ml" *)
open! Basis
open AbstractTabled
open MemoTable

(* Linear Substitution Tree indexing *)
(* Linearity: Any variables occurring inside the substitution tree are linear *)
(* Any term we insert into the substitution tree is in normalform ! *)
(* Instance Checking *)
(* Author: Brigitte Pientka *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

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
  open! RedBlackSet
  open! TableParam

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
  let isId s = RBSet.isEmpty s

  (* ---------------------------------------------------------------------- *)
  (* Context for existential variable *)
  type nonrec ctx = (int * IntSyn.dec) list ref

  (* functions for handling context for existential variables *)
  let emptyCtx () = (ref [] : ctx)
  let copy l = (ref !l : ctx)

  (* destructively updates L *)
  let delete (x, (l : ctx)) =
    let rec del (x, a, l') = match a, l' with
      | [], l -> None
      | ((y, e) as h) :: l, l' ->
          begin if x = y then Some ((y, e), rev l' @ l)
          else del (x, l, h :: l')
          end
    in
    begin match del (x, !l, []) with
    | None -> None
    | Some ((y, e), l') -> begin
        l := l';
        Some (y, e)
      end
    end

  let member x (l : ctx) =
    let rec memb (x, a) = match a with
      | [] -> None
      | ((y, (IntSyn.Dec (n, u) as e)) :: l as h) ->
          begin if x = y then Some (y, e) else memb (x, l)
          end
      | ((y, (IntSyn.ADec (n, d) as e)) :: l as h) ->
          begin if x = y then Some (y, e) else memb (x, l)
          end
    in
    memb (x, !l)

  let insertList (e, l) = l := e :: !l

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

  let makeTree () = ref (Node ((emptyCtx (), nid ()), []))
  let noChildren c = c = []

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

  exception Error = Error

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

    let emptyAnswer () = T.emptyAnsw ()
    let answList : TableParam.answer list ref = ref []
    let added = ref false

    type nonrec nvar = int
    type nonrec bvar = int
    type nonrec bdepth = int

    let expToS (g, u) = try Print.expToString g u with _ -> " <_ >"

    let rec printSub (g, a) = match a with
      | I.Shift n -> print (("I.Shift " ^ Int.toString n) ^ "\n")
      | I.Dot (I.Idx n, s) -> begin
          print (("Idx " ^ Int.toString n) ^ " . ");
          printSub (g, s)
        end
      | I.Dot (I.Exp (I.EVar ({ contents = Some u }, _, _, _) as x), s) ->
        begin
          print (("Exp ( EVar " ^ expToS (g, x)) ^ ").");
          printSub (g, s)
        end
      | I.Dot (I.Exp (I.EVar (_, _, _, _) as x), s) -> begin
          print (("Exp ( EVar  " ^ expToS (g, x)) ^ ").");
          printSub (g, s)
        end
      | I.Dot (I.Exp (I.AVar _), s) -> begin
          print "Exp (AVar _ ). ";
          printSub (g, s)
        end
      | I.Dot (I.Exp (I.EClo (I.AVar { contents = Some u }, s')), s) ->
        begin
          print (("Exp (AVar " ^ expToS (g, I.EClo (u, s'))) ^ ").");
          printSub (g, s)
        end
      | I.Dot
            ( I.Exp (I.EClo (I.EVar ({ contents = Some u }, _, _, _), s') as x),
              s ) -> begin
          print (("Exp (EVarClo " ^ expToS (g, I.EClo (u, s'))) ^ ") ");
          printSub (g, s)
        end
      | I.Dot (I.Exp (I.EClo (u, s') as x), s) -> begin
          print (("Exp (EClo " ^ expToS (g, Whnf.normalize (u, s'))) ^ ") ");
          printSub (g, s)
        end
      | I.Dot (I.Exp e, s) -> begin
          print (("Exp ( " ^ expToS (g, e)) ^ " ). ");
          printSub (g, s)
        end
      | I.Dot (I.Undef, s) -> begin
          print "Undef . ";
          printSub (g, s)
        end

    let rec normalizeSub = function
      | I.Shift n -> I.Shift n
      | I.Dot (I.Exp (I.EClo (I.AVar { contents = Some u }, s')), s) ->
          I.Dot (I.Exp (Whnf.normalize (u, s')), normalizeSub s)
      | I.Dot (I.Exp (I.EClo (I.EVar ({ contents = Some u }, _, _, _), s')), s)
        ->
          I.Dot (I.Exp (Whnf.normalize (u, s')), normalizeSub s)
      | I.Dot (I.Exp u, s) ->
          I.Dot (I.Exp (Whnf.normalize (u, I.id)), normalizeSub s)
      | I.Dot (I.Idx n, s) -> I.Dot (I.Idx n, normalizeSub s)

    let rec etaSpine (a, n) = match a with
      | I.Nil -> n = 0
      | I.App (I.Root (I.BVar k, I.Nil), s) -> k = n && etaSpine (s, n - 1)
      | I.App (a, s) -> false

    let cidFromHead = function I.Const c -> c | I.Def c -> c
    let rec dotn (i, s) = match i with 0 -> s | i -> dotn (i - 1, I.dot1 s)

    let rec raiseType a2 b2 = match a2, b2 with
      | I.Null, v -> v
      | I.Decl (g, d), v -> raiseType g (I.Lam (d, v))

    let rec compose (a, g) = match a with
      | I.Null -> g
      | IntSyn.Decl (g', d) -> IntSyn.Decl (compose (g', g), d)

    let rec shift (a, s) = match a with
      | I.Null -> s
      | IntSyn.Decl (g, d) -> I.dot1 (shift (g, s))

    let rec ctxToEVarSub (a, s) = match a with
      | I.Null -> s
      | I.Decl (g, I.Dec (_, a)) ->
          let x = I.newEVar I.Null a in
          I.Dot (I.Exp x, ctxToEVarSub (g, s))

    let rec lowerEVar' (x, g, vs') = match vs' with
      | (I.Pi ((d', _), v'), s') ->
          let d'' = I.decSub d' s' in
          let x', u =
            lowerEVar' (x, I.Decl (g, d''), Whnf.whnf (v', I.dot1 s'))
          in
          (x', I.Lam (d'', u))
      | vs' ->
          let x' = x in
          (x', x')

    and lowerEVar1 = function
      | x, I.EVar (r, g, _, _), ((I.Pi _ as v), s) ->
          let x', u = lowerEVar' (x, g, (v, s)) in
          I.EVar (ref (Some u), I.Null, v, ref [])
      | _, x, _ -> x

    and lowerEVar (e, a) = match a with
      | (I.EVar (r, g, v, { contents = [] }) as x) ->
          lowerEVar1 (e, x, Whnf.whnf (v, I.id))
      | I.EVar _ ->
          raise
            (Error
               "abstraction : LowerEVars: Typing ambiguous -- constraint of \
                functional type cannot be simplified")

    let rec ctxToAVarSub (g', a, s) = match a with
      | I.Null -> s
      | I.Decl (d, I.Dec (_, a)) ->
          let (I.EVar (r, _, _, cnstr) as e) = I.newEVar I.Null a in
          I.Dot (I.Exp e, ctxToAVarSub (g', d, s))
      | I.Decl (d_, I.ADec (_, d)) ->
          let x = I.newAVar () in
          I.Dot (I.Exp (I.EClo (x, I.Shift (-d))), ctxToAVarSub (g', d_, s))

    let assign (d, a, b, u, asub) = match a, b with
      | (I.Dec (n, v) as dec1), (I.Root (I.BVar k, s1) as e1) ->
          let (I.EVar (r, _, _, cnstr) as e) = I.newEVar I.Null v in
          let x =
            lowerEVar1 (e, I.EVar (r, I.Null, v, cnstr), Whnf.whnf (v, I.id))
          in
          ignore (r := Some u);
          S.insert asub (k - d, I.Exp x)
      | (I.ADec (n, d') as dec1), (I.Root (I.BVar k, s1) as e1)
        ->
          let (I.AVar r as a) = I.newAVar () in
          ignore (r := Some u);
          let us = Whnf.whnf (u, I.Shift (-d')) in
          S.insert asub (k - d, I.Exp (I.EClo (a, I.Shift (-d'))))

    let rec assignExp (fasub, a, b, c) = match a, b, c with
      | (((r, passed) as ctxTotal), d), (d1, (I.Root (h1, s1) as u1)), (d2, (I.Root (h2, s2) as u2)) ->
          begin match (h1, h2) with
          | I.Const c1, I.Const c2 ->
              begin if c1 = c2 then
                assignSpine (fasub, (ctxTotal, d), (d1, s1), (d2, s2))
              else raise (Assignment "Constant clash")
              end
          | I.Def c1, I.Def c2 ->
              begin if c1 = c2 then
                assignSpine (fasub, (ctxTotal, d), (d1, s1), (d2, s2))
              else
                let u1' = Whnf.normalize (Whnf.expandDef (u1, I.id)) in
                let u2' = Whnf.normalize (Whnf.expandDef (u2, I.id)) in
                assignExp (fasub, (ctxTotal, d), (d1, u1'), (d2, u2'))
              end
          | I.Def c1, _ ->
              let u1' = Whnf.normalize (Whnf.expandDef (u1, I.id)) in
              assignExp (fasub, (ctxTotal, d), (d1, u1'), (d2, u2))
          | _, I.Def c2 ->
              let u2' = Whnf.normalize (Whnf.expandDef (u2, I.id)) in
              assignExp (fasub, (ctxTotal, d), (d1, u1), (d2, u2'))
          | I.BVar k1, I.BVar k2 ->
              begin if k1 <= r + d then
                begin if k2 <= r + d then
                  begin if k2 = k1 then fasub
                  else raise (Assignment "BVar clash")
                  end
                else raise (Assignment "BVar - EVar clash")
                end
              else
                begin match member (k1 - d + passed) d1 with
                | None -> raise (Assignment "EVar nonexistent")
                | Some (x, dec_v) ->
                    begin if k2 <= r + d then
                      raise (Assignment "EVar - BVar clash")
                    else
                      begin if k2 = k1 then function
                        | asub -> begin
                            fasub asub;
                            assign (d, dec_v, u1, u2, asub)
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
          | I.Skonst c1, I.Skonst c2 ->
              begin if c1 = c2 then
                assignSpine (fasub, (ctxTotal, d), (d1, s1), (d2, s2))
              else raise (Assignment "Skolem constant clash")
              end
          | _ -> raise (Assignment "Head mismatch ")
          end
      | (ctxTotal, d), (d1, I.Lam (dec1, u1)), (d2, I.Lam (dec2, u2))
        ->
          assignExp (fasub, (ctxTotal, d + 1), (d1, u1), (d2, u2))
      | (ctxTotal, d), (d1, I.Pi (((I.Dec (_, v1) as dec1), _), u1)), (d2, I.Pi (((I.Dec (_, v2) as dec2), _), u2)) ->
          let fasub' =
            assignExp (fasub, (ctxTotal, d), (d1, v1), (d2, v2))
          in
          assignExp (fasub', (ctxTotal, d + 1), (d1, u1), (d2, u2))
      | (ctxTotal, d), (d1, I.EClo (u, (I.Shift 0 as s'))), (d2, u2)
        ->
          assignExp (fasub, (ctxTotal, d), (d1, u), (d2, u2))
      | (ctxTotal, d), (d1, u1), (d2, I.EClo (u, (I.Shift 0 as s)))
        ->
          assignExp (fasub, (ctxTotal, d), (d1, u1), (d2, u))

    and assignSpine (fasub, a, b, c) = match a, b, c with
      | (ctxTotal, d), (d1, I.Nil), (d2, I.Nil) -> fasub
      | (ctxTotal, d), (d1, I.App (u1, s1)), (d2, I.App (u2, s2))
        ->
          let fasub' =
            assignExp (fasub, (ctxTotal, d), (d1, u1), (d2, u2))
          in
          assignSpine (fasub', (ctxTotal, d), (d1, s1), (d2, s2))

    let rec assignCtx (fasub, a, b, c) = match a, b, c with
      | ctxTotal, (d1, I.Null), (d2, I.Null) -> fasub
      | ((r, passed) as ctxTotal), (d1, I.Decl (g1, I.Dec (_, v1))), (d2, I.Decl (g2, I.Dec (_, v2))) ->
          let fasub' =
            assignExp (fasub, ((r - 1, passed + 1), 0), (d1, v1), (d2, v2))
          in
          assignCtx (fasub', (r - 1, passed + 1), (d1, g1), (d2, g2))

    let nctr = ref 1

    let newNVar () =
      begin
        nctr := !nctr + 1;
        I.NVar !nctr
      end

    let equalDec = function
      | I.Dec (_, u), I.Dec (_, u') -> Conv.conv (u, I.id) (u', I.id)
      | I.ADec (_, d), I.ADec (_, d') -> d = d'
      | _, _ -> false

    let rec equalCtx (a, s, b, s') = match a, b with
      | I.Null, I.Null -> true
      | I.Decl (g, (I.Dec (_, a) as d)), I.Decl (g', (I.Dec (_, a') as d')) ->
          Conv.convDec d s (d', s')
          && equalCtx (g, I.dot1 s, g', I.dot1 s')
      | _, _ -> false

    let rec equalEqn = function
      | T.Trivial, T.Trivial -> true
      | T.Unify (g, x, n, eqn), T.Unify (g', x', n', eqn') ->
          equalCtx (g, I.id, g', I.id)
          && Conv.conv (x, I.id) (x', I.id)
          && Conv.conv (n, I.id) (n', I.id)
          && equalEqn (eqn, eqn')
      | _, _ -> false

    let rec equalEqn' (d, a, b, asub) = match a, b with
      | (d, T.Trivial), (d', T.Trivial) -> true
      | (d_, T.Unify (g, (I.Root (I.BVar k, s) as x_), n, eqn)), (d'_, T.Unify (g', x', n', eqn')) ->
          begin if
            equalCtx (g, I.id, g', I.id)
            && Conv.conv (x_, I.id) (x', I.id)
            && Conv.conv (n, I.id) (n', I.id)
          then
            let d' = d + I.ctxLength g' in
            begin if k - d' > 0 then
              begin match member (k - d') d'_ with
              | None -> ()
              | Some (x, dec_v) ->
                  begin match RBSet.lookup asub (k - d') with
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
          else false
          end
      | _, _ -> false

    let rec equalSub = function
      | I.Shift k, I.Shift k' -> k = k'
      | I.Dot (f, s), I.Dot (f', s') ->
          equalFront (f, f') && equalSub (s, s')
      | I.Dot (f, s), I.Shift k -> false
      | I.Shift k, I.Dot (f, s) -> false

    and equalFront = function
      | I.Idx n, I.Idx n' -> n = n'
      | I.Exp u, I.Exp v -> Conv.conv (u, I.id) (v, I.id)
      | I.Undef, I.Undef -> true

    let rec equalCtx' = function
      | I.Null, I.Null -> true
      | I.Decl (dk, I.Dec (_, a)), I.Decl (d1, I.Dec (_, a1)) ->
          Conv.conv (a, I.id) (a1, I.id) && equalCtx' (dk, d1)
      | I.Decl (dk, I.ADec (_, d')), I.Decl (d1, I.ADec (_, d)) ->
          d = d' && equalCtx' (dk, d1)
      | _, _ -> false

    let instanceCtx (asub, (d1_, g1), (d2_, g2)) =
      let d1 = I.ctxLength g1 in
      let d2 = I.ctxLength g2 in
      begin if d1 = d2 then
        try
          let fasub =
            assignCtx ((fun asub -> ()), (d1, 0), (d1_, g1), (d2_, g2))
          in
          fasub asub;
          true
        with Assignment msg -> false
      else false
      end

    let collectEVar (d_, nsub) =
      let d' = emptyCtx () in
      let rec collectExp (d, d', d_, a) = match a with
        | I.Lam (_, u) -> collectExp (d + 1, d', d_, u)
        | I.Root (I.Const c, s) -> collectSpine (d, d', d_, s)
        | I.Root (I.BVar k, s) ->
            begin match member (k - d) d_ with
            | None -> collectSpine (d, d', d_, s)
            | Some (x, dec_v) -> begin
                ignore (delete (x - d, d_));
                ignore (insertList ((x - d, dec_v), d'))
              end
            end
        | (I.Root (I.Def k, s) as u) ->
            let u' = Whnf.normalize (Whnf.expandDef (u, I.id)) in
            collectExp (d, d', d_, u')
      and collectSpine (d, d', d_, a) = match a with
        | I.Nil -> ()
        | I.App (u, s) -> begin
            collectExp (d, d', d_, u);
            collectSpine (d, d', d_, s)
          end
      in
      S.forall nsub (function nv, (du, u) -> collectExp (0, d', d_, u));
      (d', d_)

    let rec convAssSub' (g, idx_k, d_, asub, d, ((evars, avars) as evarsl)) =
      begin match RBSet.lookup asub d with
      | None ->
          begin match member d d_ with
          | None -> IntSyn.Shift (evars + avars)
          | Some (x, IntSyn.Dec (n, v)) ->
              let s = convAssSub' (g, idx_k + 1, d_, asub, d + 1, evarsl) in
              let (I.EVar (r, _, _, cnstr) as e) = I.newEVar I.Null v in
              I.Dot (I.Exp (I.EClo (e, I.Shift (evars + avars))), s)
          | Some (x, IntSyn.ADec (n, v)) -> begin
              print "convAssSub' -- Found an uninstantiated AVAR\n";
              raise (Error "Unassigned AVar -- should never happen\n")
            end
          end
      | Some (I.Exp e as f) ->
          let e' = Whnf.normalize (e, I.id) in
          I.Dot (I.Exp e', convAssSub' (g, idx_k + 1, d_, asub, d + 1, evarsl))
      end

    let convAssSub (g, asub, glength, d', evarsl) =
      convAssSub' (g, 0, d', asub, glength, evarsl)

    let isExists (d, I.BVar k, d_) = member (k - d) d_

    let instance ((d_t, (dt, t_v)), (d_u, (du, u)), rho_u, ac) =
      let rec instRoot (d, a, b, ac) = match d, a, b with
        | depth, (I.Root ((I.Const k as h1), s1) as t), (I.Root (I.Const k', s2) as u) ->
            begin if k = k' then instSpine (depth, s1, s2, ac)
            else raise (Instance "Constant mismatch\n")
            end
        | depth, (I.Root ((I.Def k as h1), s1) as t), (I.Root (I.Def k', s2) as u) ->
            begin if k = k' then instSpine (depth, s1, s2, ac)
            else
              let t' = Whnf.normalize (Whnf.expandDef (t_v, I.id)) in
              let u' = Whnf.normalize (Whnf.expandDef (u, I.id)) in
              instExp (depth, t', u', ac)
            end
        | depth, (I.Root ((I.Def k as h1), s1) as t), (I.Root (h2, s2) as u) ->
            let t' = Whnf.normalize (Whnf.expandDef (t_v, I.id)) in
            instExp (depth, t', u, ac)
        | d, (I.Root ((I.BVar k as h1), s1) as t), (I.Root (I.BVar k', s2) as u) ->
            begin if k > d && k' > d then
              let k1 = k - d in
              let k2 = k' - d in
              begin match (member k1 d_t, member k2 d_u) with
              | None, None ->
                  begin if k1 = k2 then instSpine (d, s1, s2, ac)
                  else raise (Instance "Bound variable mismatch\n")
                  end
              | Some (x, dec1), Some (x', dec2) ->
                  begin if k1 = k2 && equalDec (dec1, dec2) then
                    let ac' = instSpine (d, s1, s2, ac) in
                    let ac'' = function
                      | asub -> begin
                          ac' asub;
                          assign (d, dec1, t_v, u, asub)
                        end
                    in
                    ac''
                  else function
                    | asub -> begin
                        ac asub;
                        assign (d, dec1, t_v, u, asub)
                      end
                  end
              | Some (x, (I.ADec (n, d') as dec1)), None ->
                  fun asub ->
                    begin
                      ac asub;
                      assign (d, dec1, t_v, u, asub)
                    end
              | Some (x, dec1), None ->
                  fun asub ->
                    begin
                      ac asub;
                      assign (d, dec1, t_v, u, asub)
                    end
              | _, _ -> raise (Instance "Impossible\n")
              end
            else raise (Instance "Bound variable mismatch\n")
            end
        | d, (I.Root ((I.BVar k as h1), s1) as t), (I.Root (I.Const k', s2) as u) ->
            begin match isExists (d, I.BVar k, d_t) with
            | None -> raise (Instance "Impossible\n")
            | Some (x, (I.ADec (_, _) as dec1)) ->
                fun asub ->
                  begin
                    ac asub;
                    assign (d, dec1, t_v, u, asub)
                  end
            | Some (x, dec1) ->
                fun asub ->
                  begin
                    ac asub;
                    assign (d, dec1, t_v, u, asub)
                  end
            end
        | d, (I.Root ((I.BVar k as h1), s1) as t), (I.Root (I.Def k', s2) as u) ->
            begin match isExists (d, I.BVar k, d_t) with
            | None -> raise (Instance "Impossible\n")
            | Some (x, (I.ADec (_, _) as dec1)) ->
                fun asub ->
                  begin
                    ac asub;
                    assign (d, dec1, t_v, u, asub)
                  end
            | Some (x, dec1) ->
                fun asub ->
                  begin
                    ac asub;
                    assign (d, dec1, t_v, u, asub)
                  end
            end
        | depth, (I.Root (h1, s1) as t), (I.Root (I.Def k', s2) as u)
          ->
            let u' = Whnf.normalize (Whnf.expandDef (u, I.id)) in
            instExp (depth, t_v, u', ac)
        | d, (I.Root (h1, s1) as t), (I.Root (h2, s2) as u) ->
            raise (Instance "Other Cases impossible\n")
      and instExp (d, t_v, a, ac) = match t_v, a with
        | (I.NVar n as t), (I.Root (h, s) as u) -> begin
            S.insert rho_u (n, (d, u));
            ac
          end
        | (I.Root (h1, s1) as t), (I.Root (h2, s2) as u) ->
            instRoot (d, I.Root (h1, s1), I.Root (h2, s2), ac)
        | I.Lam ((I.Dec (_, a1) as d1), t1), I.Lam ((I.Dec (_, a2) as d2), u2) ->
            instExp (d + 1, t1, u2, ac)
        | t_v, u -> begin
            print "instExp -- falls through?\n";
            raise (Instance "Impossible\n")
          end
      and instSpine (d, a, b, ac) = match a, b with
        | I.Nil, I.Nil -> ac
        | I.App (t_v, s1), I.App (u, s2) ->
            let ac' = instExp (d, t_v, u, ac) in
            let ac'' = instSpine (d, s1, s2, ac') in
            ac''
        | I.Nil, I.App (_, _) -> begin
            print
              "Spines are not the same -- (first one is Nil) -- cannot happen!\n";
            raise (Instance "DifferentSpines\n")
          end
        | I.App (_, _), I.Nil -> begin
            print
              "Spines are not the same -- second one is Nil -- cannot happen!\n";
            raise (Instance "DifferentSpines\n")
          end
        | I.SClo (_, _), _ -> begin
            print "Spine Closure!(1) -- cannot happen!\n";
            raise (Instance "DifferentSpines\n")
          end
        | _, I.SClo (_, _) -> begin
            print "Spine Closure! (2) -- cannot happen!\n";
            raise (Instance " DifferentSpines\n")
          end
      in
      ac := instExp (dt, t_v, u, !ac)

    let compHeads = function
      | (d_1, I.Const k), (d_2, I.Const k') -> k = k'
      | (d_1, I.Def k), (d_2, I.Def k') -> k = k'
      | (d_1, I.BVar k), (d_2, I.BVar k') ->
          begin match isExists (0, I.BVar k, d_1) with
          | None -> k = k'
          | Some (x, dec_v) -> true
          end
      | (d_1, I.BVar k), (d_2, h2) ->
          begin match isExists (0, I.BVar k, d_1) with
          | None -> false
          | Some (x, dec_v) -> true
          end
      | (d_1, h1), (d_2, h2) -> false

    let compatible' ((d_t, (dt, t_v)), (d_u, (du, u)), ds, rho_t, rho_u) =
      let genNVar ((rho_t, t_v), (rho_u, u)) =
        begin
          S.insert rho_t (!nctr + 1, t_v);
          begin
            S.insert rho_u (!nctr + 1, u);
            newNVar ()
          end
        end
      in
      let rec genRoot (d, a, b) = match a, b with
        | (I.Root ((I.Const k as h1), s1) as t), (I.Root (I.Const k', s2) as u) ->
            begin if k = k' then
              let s' = genSpine (d, s1, s2) in
              I.Root (h1, s')
            else genNVar ((rho_t, (d, t_v)), (rho_u, (d, u)))
            end
        | (I.Root ((I.Def k as h1), s1) as t), (I.Root (I.Def k', s2) as u) ->
            begin if k = k' then
              let s' = genSpine (d, s1, s2) in
              I.Root (h1, s')
            else genNVar ((rho_t, (d, t_v)), (rho_u, (d, u)))
            end
        | (I.Root ((I.BVar k as h1), s1) as t), (I.Root (I.BVar k', s2) as u) ->
            begin if k > d && k' > d then
              let k1 = k - d in
              let k2 = k' - d in
              begin match (member k1 d_t, member k2 d_u) with
              | None, None ->
                  begin if k1 = k2 then
                    try
                      let s' = genSpine (d, s1, s2) in
                      I.Root (h1, s')
                    with differentSpine ->
                      genNVar ((rho_t, (d, t_v)), (rho_u, (d, u)))
                  else genNVar ((rho_t, (d, t_v)), (rho_u, (d, u)))
                  end
              | Some (x, dec1), Some (x', dec2) ->
                  begin if k1 = k2 && equalDec (dec1, dec2) then
                    let s' = genSpine (d, s1, s2) in
                    ignore (delete (x, d_t));
                    begin
                      ignore (delete (x', d_u));
                      begin
                        ignore (insertList ((x, dec1), ds));
                        I.Root (h1, s')
                      end
                    end
                  else genNVar ((rho_t, (d, t_v)), (rho_u, (d, u)))
                  end
              | _, _ -> genNVar ((rho_t, (d, t_v)), (rho_u, (d, u)))
              end
            else
              begin if k = k' then
                try
                  let s' = genSpine (d, s1, s2) in
                  I.Root (h1, s')
                with DifferentSpines ->
                  genNVar ((rho_t, (d, t_v)), (rho_u, (d, u)))
              else genNVar ((rho_t, (d, t_v)), (rho_u, (d, u)))
              end
            end
        | (I.Root ((I.BVar k as h1), s1) as t), (I.Root (I.Const k', s2) as u) ->
            genNVar ((rho_t, (d, t_v)), (rho_u, (d, u)))
        | (I.Root ((I.BVar k as h1), s1) as t), (I.Root (I.Def k', s2) as u) ->
            genNVar ((rho_t, (d, t_v)), (rho_u, (d, u)))
        | (I.Root (h1, s1) as t), (I.Root (h2, s2) as u) ->
            genNVar ((rho_t, (d, t_v)), (rho_u, (d, u)))
      and genExp (d, a, b) = match a, b with
        | (I.NVar n as t), (I.Root (h, s) as u) -> begin
            S.insert rho_u (n, (d, u));
            t_v
          end
        | (I.Root (h1, s1) as t), (I.Root (h2, s2) as u) ->
            genRoot (d, I.Root (h1, s1), I.Root (h2, s2))
        | I.Lam ((I.Dec (_, a1) as d1), t1), I.Lam ((I.Dec (_, a2) as d2), u2) ->
            let e = genExp (d + 1, t1, u2) in
            I.Lam (d1, e)
        | t_v, u -> begin
            print "genExp -- falls through?\n";
            genNVar ((rho_t, (d, t_v)), (rho_u, (d, u)))
          end
      and genSpine (d, a, b) = match a, b with
        | I.Nil, I.Nil -> I.Nil
        | I.App (t_v, s1), I.App (u, s2) ->
            let e = genExp (d, t_v, u) in
            let s' = genSpine (d, s1, s2) in
            I.App (e, s')
        | I.Nil, I.App (_, _) -> raise DifferentSpines
        | I.App (_, _), I.Nil -> raise DifferentSpines
        | I.SClo (_, _), _ -> raise DifferentSpines
        | _, I.SClo (_, _) -> raise DifferentSpines
      in
      Variant (dt, genExp (dt, t_v, u))

    let compatible (a, b, ds, rho_t, rho_u) = match a, b with
      | (d_t, ((d1, I.Root (h1, s1)) as t)), (d_u, ((d2, I.Root (h2, s2)) as u)) ->
          begin if compHeads ((d_t, h1), (d_u, h2)) then
            compatible' ((d_t, t), (d_u, u), ds, rho_t, rho_u)
          else NotCompatible
          end
      | (d_t, t_v), (d_u, u) ->
          compatible' ((d_t, t_v), (d_u, u), ds, rho_t, rho_u)

    let rec compatibleCtx (asub, a, b) = match a, b with
      | (dsq, gsq, eqn_sq), [] -> None
      | (dsq, gsq, eqn_sq), (_, delta', g', eqn', answRef', _, status') :: gRlist ->
          begin if instanceCtx (asub, (dsq, gsq), (delta', g')) then
            Some ((delta', g', eqn'), answRef', status')
          else compatibleCtx (asub, (dsq, gsq, eqn_sq), gRlist)
          end

    let instanceSub ((d_t, nsub_t), (dsq, squery), asub) =
      let rho_u = nid () in
      let d_r2 = copy dsq in
      let ac = ref (function (asub : exSubsts) -> ()) in
      try
        begin
          S.forall squery (function nv, (du, u) ->
              begin match S.lookup nsub_t nv with
              | Some (dt, t_v) ->
                  instance ((d_t, (dt, t_v)), (d_r2, (du, u)), rho_u, ac)
              | None -> S.insert rho_u (nv, (du, u))
              end);
          begin
            ( ! ) ac asub;
            InstanceSub (asub, (d_r2, rho_u))
          end
        end
      with Instance msg -> NoCompatibleSub

    let instChild (a, b, asub) = match a, b with
      | (Leaf ((d_t, nsub_t), gList) as n), (d_sq, sq) ->
          instanceSub ((d_t, nsub_t), (d_sq, sq), asub)
      | (Node ((d_t, nsub_t), children') as n), (d_sq, sq) ->
          instanceSub ((d_t, nsub_t), (d_sq, sq), asub)

    let findAllInst (g_r, children, ds, asub) =
      let rec findAllCands (g_r, a, b, asub, iList) = match a, b with
        | [], (dsq, sub_u) -> iList
        | x :: l, (dsq, sub_u) ->
            let asub' = S.copy asub in
            begin match instChild (!x, (dsq, sub_u), asub) with
            | NoCompatibleSub ->
                findAllCands (g_r, l, (dsq, sub_u), asub', iList)
            | InstanceSub (asub, drho2) ->
                findAllCands
                  (g_r, l, (dsq, sub_u), asub', (x, drho2, asub) :: iList)
            end
      in
      findAllCands (g_r, children, ds, asub, [])

    let rec solveEqn (a, g) = match a with
      | (trivial, s) -> true
      | (T.Unify (g', e1, n, eqns), s) ->
          let g'' = compose (g', g) in
          let s' = shift (g'', s) in
          Assign.unifiable g'' (n, s') (e1, s') && solveEqn ((eqns, s), g)

    let rec solveEqn' (a, g) = match a with
      | (trivial, s) -> true
      | (T.Unify (g', e1, n, eqns), s) ->
          let g'' = compose (g', g) in
          let s' = shift (g', s) in
          Assign.unifiable g'' (n, s') (e1, s')
          && solveEqn' ((eqns, s), g)

    let rec solveEqnI' (a, g) = match a with
      | (trivial, s) -> true
      | (T.Unify (g', e1, n, eqns), s) ->
          let g'' = compose (g', g) in
          let s' = shift (g', s) in
          Assign.instance g'' (e1, s') (n, s')
          && solveEqnI' ((eqns, s), g)

    let retrieveInst (nref, (dq, sq), asub, gr) =
      let rec retrieve' = function
        | ( (Leaf ((d, s), gRlistRef) as n),
            (dq, sq),
            asubst,
            ((((dEVars, dAVars) as dAEVars), g_r, eqn, stage, status) as gr') )
          ->
            let dsq, d_g = collectEVar (dq, sq) in
            begin match
              compatibleCtx (asubst, (d_g, g_r, eqn), !gRlistRef)
            with
            | None -> raise (Instance "Compatible path -- different ctx\n")
            | Some ((d', g', eqn'), answRef', status') ->
                let dAEVars = compose (dEVars, dAVars) in
                let esub = ctxToAVarSub (g', dAEVars, I.Shift 0) in
                let asub =
                  convAssSub
                    ( g',
                      asubst,
                      I.ctxLength g' + 1,
                      d',
                      (I.ctxLength dAVars, I.ctxLength dEVars) )
                in
                ignore begin if solveEqn' ((eqn, shift (g', esub)), g') then ()
                  else print " failed to solve eqn_query\n"
                  end;
                let easub = normalizeSub (I.comp asub esub) in
                begin if solveEqnI' ((eqn', shift (g', easub)), g') then
                  T.RepeatedEntry ((esub, asub), answRef', status')
                else
                  raise
                    (Instance "Compatible path -- resdidual equ. not solvable\n")
                end
            end
        | ( (Node ((d, sub), children) as n),
            (dq, sq),
            asub,
            ((dAEVars, g_r, eqn, stage, status) as gr) ) ->
            let instCand = findAllInst (g_r, children, (dq, sq), asub) in
            let rec checkCandidates = function
              | [] -> raise (Instance "No compatible child\n")
              | (childRef, drho2, asub) :: iCands -> (
                  try retrieve' (!childRef, drho2, asub, gr)
                  with Instance msg -> checkCandidates iCands)
            in
            checkCandidates instCand
      in
      function () -> ((), retrieve' (!nref, (dq, sq), asub, gr))

    let compatibleSub ((d_t, nsub_t), (dsq, squery)) =
      let sigma, rho_t, rho_u = (nid (), nid (), nid ()) in
      let dsigma = emptyCtx () in
      let d_r1 = copy d_t in
      let d_r2 = copy dsq in
      let choose = ref (function (match_ : bool) -> ()) in
      ignore (S.forall squery (function nv, u ->
            begin match S.lookup nsub_t nv with
            | Some t_v ->
                begin match
                  compatible ((d_r1, t_v), (d_r2, u), dsigma, rho_t, rho_u)
                with
                | NotCompatible -> begin
                    S.insert rho_t (nv, t_v);
                    S.insert rho_u (nv, u)
                  end
                | Variant (dt, t') ->
                    let restc = !choose in
                    S.insert sigma (nv, (dt, t'));
                    choose :=
                      function
                      | match_ -> begin
                          restc match_;
                          begin if match_ then () else ()
                          end
                        end
                end
            | None -> S.insert rho_u (nv, u)
            end));
      begin if isId rho_t then begin
        ( ! ) choose true;
        VariantSub (d_r2, rho_u)
      end
      else begin
        ( ! ) choose false;
        begin if isId sigma then NoCompatibleSub
        else SplitSub ((dsigma, sigma), (d_r1, rho_t), (d_r2, rho_u))
        end
      end
      end

    let mkNode = function
      | ( Node (_, children),
          ((ds, sigma) as dsigma),
          ((d1, rho1) as drho1),
          (((evarl, l), dp, eqn, answRef, stage, status) as gr),
          ((d2, rho2) as drho2) ) ->
          let d_rho2, d_g2 = collectEVar (d2, rho2) in
          let gr' = ((evarl, l), d_g2, dp, eqn, answRef, stage, status) in
          let sizeSigma, sizeRho1, sizeRho2 =
            (S.size sigma, S.size rho1, S.size rho2)
          in
          Node
            ( dsigma,
              [
                ref (Leaf ((d_rho2, rho2), ref [ gr' ]));
                ref (Node (drho1, children));
              ] )
      | ( Leaf (c, gRlist),
          ((ds, sigma) as dsigma),
          ((d1, rho1) as drho1),
          (((evarl, l), dp, eqn, answRef, stage, status) as gr2),
          ((d2, rho2) as drho2) ) ->
          let d_rho2, d_g2 = collectEVar (d2, rho2) in
          let gr2' = ((evarl, l), d_g2, dp, eqn, answRef, stage, status) in
          Node
            ( dsigma,
              [
                ref (Leaf ((d_rho2, rho2), ref [ gr2' ]));
                ref (Leaf (drho1, gRlist));
              ] )

    let compChild = function
      | (Leaf ((d_t, nsub_t), gList) as n), (d_e, nsub_e) ->
          compatibleSub ((d_t, nsub_t), (d_e, nsub_e))
      | (Node ((d_t, nsub_t), children') as n), (d_e, nsub_e) ->
          compatibleSub ((d_t, nsub_t), (d_e, nsub_e))

    let findAllCandidates (g_r, children, ds) =
      let rec findAllCands (g_r, a, b, vList, sList) = match a, b with
        | [], (dsq, sub_u) -> (vList, sList)
        | x :: l, (dsq, sub_u) ->
            begin match compChild (!x, (dsq, sub_u)) with
            | NoCompatibleSub ->
                findAllCands (g_r, l, (dsq, sub_u), vList, sList)
            | SplitSub (dsigma, drho1, drho2) ->
                findAllCands
                  ( g_r,
                    l,
                    (dsq, sub_u),
                    vList,
                    (x, (dsigma, drho1, drho2)) :: sList )
            | VariantSub (d_r2, rho2) ->
                let drho2 = (d_r2, rho2) in
                findAllCands
                  (g_r, l, (dsq, sub_u), (x, drho2, I.id) :: vList, sList)
            end
      in
      findAllCands (g_r, children, ds, [], [])

    let divergingCtx (stage, g, gRlistRef) =
      let l = I.ctxLength g + 3 in
      List.exists
        (function
          | (_, l), d, g', _, _, stage', _ ->
              stage = stage' && l > I.ctxLength g')
        !gRlistRef

    let eqHeads = function
      | I.Const k, I.Const k' -> k = k'
      | I.BVar k, I.BVar k' -> k = k'
      | I.Def k, I.Def k' -> k = k'
      | _, _ -> false

    let rec eqTerm = function
      | I.Root (h2, s2), ((I.Root (h, s) as t), rho1) -> begin
          eqHeads (h2, h) && eqSpine (s2, (s, rho1))
        end
      | t2, (I.NVar n, rho1) ->
          begin match S.lookup rho1 n with
          | None -> false
          | Some (dt1, t1) -> eqTerm (t2, (t1, nid ()))
          end
      | I.Lam (d2, t2), (I.Lam (d, t_v), rho1) -> eqTerm (t2, (t_v, rho1))
      | _, (_, _) -> false

    and eqSpine = function
      | I.Nil, (I.Nil, rho1) -> true
      | I.App (t2, s2), (I.App (t_v, s), rho1) ->
          eqTerm (t2, (t_v, rho1)) && eqSpine (s2, (s, rho1))

    let divergingSub ((ds, sigma), (dr1, rho1), (dr2, rho2)) =
      S.exists rho2 (function n2, (dt2, t2) ->
          S.exists sigma (function _, (d, t) -> eqTerm (t2, (t, rho1))))

    let rec variantCtx = function
      | (g, eqn), [] -> None
      | (g, eqn), (l', d_g, g', eqn', answRef', _, status') :: gRlist ->
          begin if equalCtx' (g, g') && equalEqn (eqn, eqn') then
            Some (l', answRef', status')
          else variantCtx ((g, eqn), gRlist)
          end

    let rec insert (nref, (dsq, sq), gr) =
      let insert' = function
        | ( (Leaf (_, gRlistRef) as n),
            (dsq, sq),
            ((l, g_r, eqn, answRef, stage, status) as gr) ) ->
            begin match variantCtx ((g_r, eqn), !gRlistRef) with
            | None -> (
                let d_nsub, d_g = collectEVar (dsq, sq) in
                let gr' = (l, d_g, g_r, eqn, answRef, stage, status) in
                function
                | () ->
                    ( begin
                        gRlistRef := gr' :: !gRlistRef;
                        answList := answRef :: !answList
                      end,
                      T.NewEntry answRef ))
            | Some (_, answRef', status') -> (
                function
                | () -> ((), T.RepeatedEntry ((I.id, I.id), answRef', status')))
            end
        | ( (Node ((d, sub), children) as n),
            (dsq, sq),
            ((l, g_r, eqn, answRef, stage, status) as gr) ) ->
            let variantCand, splitCand =
              findAllCandidates (g_r, children, (dsq, sq))
            in
            let d_nsub, d_g = collectEVar (dsq, sq) in
            let gr' = (l, d_g, g_r, eqn, answRef, stage, status) in
            let rec checkCandidates = function
              | [], [] -> (
                  function
                  | () ->
                      ( begin
                          nref :=
                            Node
                              ( (d, sub),
                                ref (Leaf ((d_nsub, sq), ref [ gr' ]))
                                :: children );
                          answList := answRef :: !answList
                        end,
                        T.NewEntry answRef ))
              | [], (childRef, (dsigma, drho1, drho2)) :: _ ->
                  begin if
                    !TableParam.divHeuristic
                    && divergingSub (dsigma, drho1, drho2)
                  then function
                    | () ->
                        ( begin
                            childRef :=
                              mkNode (!childRef, dsigma, drho1, gr, drho2);
                            answList := answRef :: !answList
                          end,
                          T.DivergingEntry (I.id, answRef) )
                  else function
                    | () ->
                        ( begin
                            childRef :=
                              mkNode (!childRef, dsigma, drho1, gr, drho2);
                            answList := answRef :: !answList
                          end,
                          T.NewEntry answRef )
                  end
              | (childRef, drho2, asub) :: [], _ -> insert (childRef, drho2, gr)
              | (childRef, drho2, asub) :: l, sCands ->
                  begin match (insert (childRef, drho2, gr)) () with
                  | _, T.NewEntry answRef -> checkCandidates (l, sCands)
                  | _, T.RepeatedEntry (asub, answRef, status) ->
                      fun () -> ((), T.RepeatedEntry (asub, answRef, status))
                  | _, T.DivergingEntry (asub, answRef) ->
                      fun () -> ((), T.DivergingEntry (asub, answRef))
                  end
            in
            checkCandidates (variantCand, splitCand)
      in
      insert' (!nref, (dsq, sq), gr)

    let answCheckVariant (s', answRef, o) =
      let rec member a2 b2 = match a2, b2 with
        | (d, sk), [] -> false
        | (d, sk), ((d1, s1), _) :: s ->
            begin if equalSub (sk, s1) && equalCtx' (d, d1) then true
            else member (d, sk) s
            end
      in
      let dEVars, sk = A.abstractAnswSub s' in
      begin if member (dEVars, sk) (T.solutions answRef) then T.Repeated
      else begin
        T.addSolution dEVars sk o answRef;
        T.New_
      end
      end

    let reset () =
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

    let rec makeCtx (n, a, b) = match a, b with
      | I.Null, (dEVars : ctx) -> ()
      | I.Decl (g, d), (dEVars : ctx) -> begin
          insertList ((n, d), dEVars);
          makeCtx (n + 1, g, dEVars)
        end

    let callCheck a dAVars dEVars g u eqn status =
      let n, tree = Array.sub (indexArray, a) in
      let sq = S.new_ () in
      let dAEVars = compose (dEVars, dAVars) in
      let dq = emptyCtx () in
      let n = I.ctxLength g in
      ignore (makeCtx (n + 1, dAEVars, (dq : ctx)));
      let l = I.ctxLength dAEVars in
      ignore (S.insert sq (1, (0, u)));
      let gr =
        ((l, n + 1), g, eqn, emptyAnswer (), !TableParam.stageCtr, status)
      in
      let gr' = ((dEVars, dAVars), g, eqn, !TableParam.stageCtr, status) in
      let result =
        try retrieveInst (tree, (dq, sq), asid (), gr')
        with Instance msg -> insert (tree, (dq, sq), gr)
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

    let insertIntoTree a dAVars dEVars g u eqn answRef status =
      let n, tree = Array.sub (indexArray, a) in
      let sq = S.new_ () in
      let dAEVars = compose (dEVars, dAVars) in
      let dq = emptyCtx () in
      let n = I.ctxLength g in
      ignore (makeCtx (n + 1, dAEVars, (dq : ctx)));
      let l = I.ctxLength dAEVars in
      ignore (S.insert sq (1, (0, u)));
      let gr =
        ((l, n + 1), g, eqn, emptyAnswer (), !TableParam.stageCtr, status)
      in
      let result =
        insert
          ( tree,
            (dq, sq),
            ((l, n + 1), g, eqn, answRef, !TableParam.stageCtr, status) )
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

    let answCheck (s', answRef, o) = answCheckVariant (s', answRef, o)

    let updateTable () =
      let rec update arg__1 arg__2 =
        begin match (arg__1, arg__2) with
        | [], flag -> flag
        | answRef :: aList, flag ->
            let l = length (T.solutions answRef) in
            begin if l = T.lookup answRef then update aList flag
            else begin
              T.updateAnswLookup l answRef;
              update aList true
            end
            end
        end
      in
      let flag = update !answList false in
      let r = flag || !added in
      added := false;
      r
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
  (* pre-Stelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
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

  let callCheck dAVars dEVars g u eqn status =
    callCheck (cidFromHead (I.targetHead u)) dAVars dEVars g u eqn status

  let insertIntoTree dAVars dEVars g u eqn answRef status =
    insertIntoTree
      (cidFromHead (I.targetHead u))
      dAVars dEVars g u eqn answRef status

  let answerCheck a b c = answCheck (a, b, c)
  let updateTable = updateTable
  let tableSize () = length !answList

  (* memberCtxS ((G,V), G', n) = bool

       if G |- V and |- G' ctx
          exists a V' in G s.t.  V'[^n]  is an instance of V
       then return true
         otherwise false
    *)
  let memberCtx g v g' =
    let rec instanceCtx' (a, b, n) = match a, b with
      | (g, v), I.Null -> None
      | (g, v), I.Decl (g', (I.Dec (_, v') as d')) ->
          begin if Match.instance g (v, I.id) (v', I.Shift n) then
            Some d'
          else instanceCtx' ((g, v), g', n + 1)
          end
    in
    instanceCtx' ((g, v), g', 1)
end
(*! sharing Print.IntSyn = IntSyn'!*)
(* local *)
(* functor MemoTable *)

(* # 1 "src/opsem/SubtreeInst.sml.ml" *)
