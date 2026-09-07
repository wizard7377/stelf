open! Global.Global_
open! Table
open! Intsyn.Lambda_
open! Print.Print_
open! Compile
open! Compile.Compile_
open! CompSyn

(* # 1 "src/opsem/MemoTable.sig.ml" *)
open TableParam

(* Indexing *)
(* Author: Brigitte Pientka *)
include MEMOTABLE
(* signature MemoTable *)

(* # 1 "src/opsem/MemoTable.fun.ml" *)
open! Basis
open AbstractTabled
open RedBlackSet

(* Linear Substitution Tree indexing *)
(* Linearity: Any variables occurring inside the substitution tree are linear *)
(* Any term we insert into the substitution tree is in normalform *)
(* Variant Checking *)
(* Author: Brigitte Pientka *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MemoTable (MemoTable__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  (*! structure RBSet : RBSET !*)
  (*! structure TableParam : TABLEPARAM !*)
  (*! sharing TableParam.IntSyn = IntSyn' !*)
  (*! sharing TableParam.CompSyn = CompSyn' !*)
  (*! sharing TableParam.RBSet = RBSet !*)
  module AbstractTabled : ABSTRACTTABLED

  (*! sharing AbstractTabled.IntSyn = IntSyn' !*)
  module Print : PRINT
end) : MEMOTABLE = struct
  open MemoTable__0
  module I = IntSyn

  (*! structure IntSyn = IntSyn' !*)
  (* ---------------------------------------------------------------------- *)
  (* Linear substitution tree for linear terms *)
  (* normalSubsts: key = int = nvar *)
  (* property: linear *)
  type nonrec normalSubsts = IntSyn.exp RBSet.ordSet
  type nonrec exSubsts = IntSyn.exp RBSet.ordSet

  let nid : unit -> normalSubsts = RBSet.new_
  let aid = TableParam.aid
  let existId : unit -> normalSubsts = RBSet.new_
  let isId s = RBSet.isEmpty s

  (* ---------------------------------------------------------------------- *)
  type nonrec ctx = (int * IntSyn.dec) list ref

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
      | ((y, e) :: l as h) ->
          begin if x = y then Some (y, e) else memb (x, l)
          end
    in
    memb (x, !l)

  let insertList (e, l) =
    begin
      l := e :: !l;
      l
    end

  (* ctxToEVarSub D = s

     if D is a context for existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)
  let rec ctxToEVarSub (a, s) = match a with
    | I.Null -> s
    | IntSyn.Decl (g, IntSyn.Dec (_, a)) ->
        let s' = ctxToEVarSub (g, s) in
        let x = IntSyn.newEVar IntSyn.Null (IntSyn.EClo (a, s')) in
        IntSyn.Dot (IntSyn.Exp x, s')

  (* ---------------------------------------------------------------------- *)
  (* Substitution Tree *)
  (* it is only possible to distribute the evar-ctx because
     all evars occur exactly once! -- linear
     this allows us to maintain invariant, that every occurrence of an evar is
     defined in its evar-ctx
     *)
  type tree =
    | Leaf of
        (ctx * normalSubsts)
        * ((int * int)
          * IntSyn.dctx
          * TableParam.resEqn
          * TableParam.answer
          * int
          * TableParam.status)
          list
          ref
    (* G *)
    (* #G *)
    (* #EVar *)
    | Node of (ctx * normalSubsts) * tree ref list

  let makeTree () = ref (Node ((emptyCtx (), nid ()), []))
  let noChildren c = c = []

  type retrieval = Variant of IntSyn.exp | NotCompatible

  type compSub =
    | SplitSub of
        (ctx * normalSubsts) * (ctx * normalSubsts) * (ctx * normalSubsts)
    (* rho2 *)
    (* rho1 *)
    (* sigma *)
    | VariantSub of ctx * normalSubsts
    (* rho2 *)
    (* normalSubsts * *)
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
    exception Generalization of string
    exception DifferentSpines

    let emptyAnswer () = T.emptyAnsw ()
    let answList : TableParam.answer list ref = ref []
    let added = ref false

    type nonrec nvar = int
    type nonrec bvar = int
    type nonrec bdepth = int

    let cidFromHead = function I.Const c -> c | I.Def c -> c
    let rec dotn (i, s) = match i with 0 -> s | i -> dotn (i - 1, I.dot1 s)

    let rec compose = function
      | I.Null, g -> g
      | IntSyn.Decl (g, d), g' -> IntSyn.Decl (compose (g, g'), d)

    let rec shift (a, s) = match a with
      | I.Null -> s
      | IntSyn.Decl (g, d) -> I.dot1 (shift (g, s))

    let rec raiseType a2 b2 = match a2, b2 with
      | I.Null, u -> u
      | I.Decl (g, d), u -> raiseType g (I.Lam (d, u))

    let rec ctxToAVarSub (g', a, s) = match a with
      | I.Null -> s
      | I.Decl (d, I.Dec (_, a)) ->
          let (I.EVar (r, _, _, cnstr) as e) = I.newEVar I.Null a in
          I.Dot (I.Exp e, ctxToAVarSub (g', d, s))
      | I.Decl (d_, I.ADec (_, d)) ->
          let x = I.newAVar () in
          I.Dot (I.Exp (I.EClo (x, I.Shift (-d))), ctxToAVarSub (g', d_, s))

    let rec solveEqn' (a, g) = match a with
      | (trivial, s) -> true
      | (T.Unify (g', e1, n, eqns), s) ->
          let g'' = compose (g', g) in
          let s' = shift (g', s) in
          Assign__.unifiable g'' (n, s') (e1, s')
          && solveEqn' ((eqns, s), g)

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
      | I.Decl (g, d), I.Decl (g', d') ->
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

    let equalSub1 (I.Dot (ms, s), I.Dot (ms', s')) = equalSub (s, s')

    let rec equalCtx' = function
      | I.Null, I.Null -> true
      | I.Decl (dk, I.Dec (_, a)), I.Decl (d1, I.Dec (_, a1)) ->
          Conv.conv (a, I.id) (a1, I.id) && equalCtx' (dk, d1)
      | I.Decl (dk, I.ADec (_, d')), I.Decl (d1, I.ADec (_, d)) ->
          d = d' && equalCtx' (dk, d1)
      | _, _ -> false

    let compareCtx (g, g') = equalCtx' (g, g')
    let isExists (d, I.BVar k, d_) = member (k - d) d_

    let compHeads = function
      | (d_1, I.Const k), (d_2, I.Const k') -> k = k'
      | (d_1, I.Def k), (d_2, I.Def k') -> k = k'
      | (d_1, I.BVar k), (d_2, I.BVar k') ->
          begin match isExists (0, I.BVar k, d_1) with
          | None -> k = k'
          | Some (x, _dec) -> true
          end
      | (d_1, I.BVar k), (d_2, h2) ->
          begin match isExists (0, I.BVar k, d_1) with
          | None -> false
          | Some (x, _dec) -> true
          end
      | (d_1, h1), (d_2, h2) -> false

    let compatible' ((d_t, t_v), (d_u, u), ds, rho_t, rho_u) =
      let genNVar ((rho_t, t_v), (rho_u, u)) =
        begin
          S.insert rho_t (!nctr + 1, t_v);
          begin
            S.insert rho_u (!nctr + 1, u);
            newNVar ()
          end
        end
      in
      let rec genRoot = function
        | ( depth,
            (I.Root ((I.Const k as h1), s1) as t),
            (I.Root (I.Const k', s2) as u) ) ->
            begin if k = k' then
              let s' = genSpine (depth, s1, s2) in
              I.Root (h1, s')
            else genNVar ((rho_t, t_v), (rho_u, u))
            end
        | ( depth,
            (I.Root ((I.Def k as h1), s1) as t),
            (I.Root (I.Def k', s2) as u) ) ->
            begin if k = k' then
              let s' = genSpine (depth, s1, s2) in
              I.Root (h1, s')
            else genNVar ((rho_t, t_v), (rho_u, u))
            end
        | ( d,
            (I.Root ((I.BVar k as h1), s1) as t),
            (I.Root (I.BVar k', s2) as u) ) ->
            begin if k > d && k' > d then
              let k1 = k - d in
              let k2 = k' - d in
              begin match (member k1 d_t, member k2 d_u) with
              | None, None ->
                  begin if k1 = k2 then
                    try
                      let s' = genSpine (d, s1, s2) in
                      I.Root (h1, s')
                    with differentSpine -> genNVar ((rho_t, t_v), (rho_u, u))
                  else genNVar ((rho_t, t_v), (rho_u, u))
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
                  else genNVar ((rho_t, t_v), (rho_u, u))
                  end
              | _, _ -> genNVar ((rho_t, t_v), (rho_u, u))
              end
            else
              begin if k = k' then
                try
                  let s' = genSpine (d, s1, s2) in
                  I.Root (h1, s')
                with DifferentSpines -> genNVar ((rho_t, t_v), (rho_u, u))
              else genNVar ((rho_t, t_v), (rho_u, u))
              end
            end
        | ( d,
            (I.Root ((I.BVar k as h1), s1) as t),
            (I.Root (I.Const k', s2) as u) ) ->
            genNVar ((rho_t, t_v), (rho_u, u))
        | d, (I.Root (h1, s1) as t), (I.Root (h2, s2) as u) ->
            genNVar ((rho_t, t_v), (rho_u, u))
      and genExp (d, a, b) = match a, b with
        | (I.NVar n as t), (I.Root (h, s) as u) -> begin
            S.insert rho_u (n, u);
            t_v
          end
        | (I.Root (h1, s1) as t), (I.Root (h2, s2) as u) ->
            genRoot (d, I.Root (h1, s1), I.Root (h2, s2))
        | I.Lam ((I.Dec (_, a1) as d1), t1), I.Lam ((I.Dec (_, a2) as d2), u2) ->
            let e = genExp (d + 1, t1, u2) in
            I.Lam (d1, e)
        | t_v, u -> begin
            print "genExp -- falls through?\n";
            genNVar ((rho_t, t_v), (rho_u, u))
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
      let e = genExp (0, t_v, u) in
      Variant e

    let compatible (a, b, ds, rho_t, rho_u) = match a, b with
      | (d_t, (I.Root (h1, s1) as t)), (d_u, (I.Root (h2, s2) as u)) ->
          begin if compHeads ((d_t, h1), (d_u, h2)) then
            compatible' ((d_t, t), (d_u, u), ds, rho_t, rho_u)
          else NotCompatible
          end
      | (d_t, t_v), (d_u, u) ->
          compatible' ((d_t, t_v), (d_u, u), ds, rho_t, rho_u)

    let compatibleSub ((d_t, nsub_t), (d_u, nsub_u)) =
      let sigma, rho_t, rho_u = (nid (), nid (), nid ()) in
      let dsigma = emptyCtx () in
      let d_r1 = copy d_t in
      let d_r2 = copy d_u in
      let choose = ref (function (match_ : bool) -> ()) in
      ignore (S.forall nsub_u (function nv, u ->
            begin match S.lookup nsub_t nv with
            | Some t_v ->
                begin match
                  compatible ((d_r1, t_v), (d_r2, u), dsigma, rho_t, rho_u)
                with
                | NotCompatible -> begin
                    S.insert rho_t (nv, t_v);
                    S.insert rho_u (nv, u)
                  end
                | Variant t' ->
                    let restc = !choose in
                    S.insert sigma (nv, t');
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

    let mkLeaf (ds, gr, n) = Leaf (ds, gr)

    let mkNode (a, dsigma, drho1, gr, drho2) = match a, gr with
      | Node (_, children), gr ->
          Node
            ( dsigma,
              [ ref (Leaf (drho2, ref [ gr ])); ref (Node (drho1, children)) ]
            )
      | Leaf (c, gRlist), gr2 ->
          Node
            ( dsigma,
              [ ref (Leaf (drho2, ref [ gr2 ])); ref (Leaf (drho1, gRlist)) ] )

    let rec compatibleCtx = function
      | (g, eqn), [] -> None
      | (g, eqn), (l', g', eqn', answRef', _, status') :: gRlist ->
          begin if equalCtx' (g, g') && equalEqn (eqn, eqn') then
            Some (l', answRef', status')
          else compatibleCtx ((g, eqn), gRlist)
          end

    let compChild = function
      | (Leaf ((d_t, nsub_t), gList) as n), (d_e, nsub_e) ->
          compatibleSub ((d_t, nsub_t), (d_e, nsub_e))
      | (Node ((d_t, nsub_t), children') as n), (d_e, nsub_e) ->
          compatibleSub ((d_t, nsub_t), (d_e, nsub_e))

    let findAllCandidates (g_r, children, ds) =
      let rec findAllCands (g_r, a, b, vList, sList) = match a, b with
        | [], (d_u, sub_u) -> (vList, sList)
        | x :: l, (d_u, sub_u) ->
            begin match compChild (!x, (d_u, sub_u)) with
            | NoCompatibleSub ->
                findAllCands (g_r, l, (d_u, sub_u), vList, sList)
            | SplitSub (dsigma, drho1, drho2) ->
                findAllCands
                  ( g_r,
                    l,
                    (d_u, sub_u),
                    vList,
                    (x, (dsigma, drho1, drho2)) :: sList )
            | VariantSub (d_r2, rho2) ->
                let drho2 = (d_r2, rho2) in
                findAllCands
                  (g_r, l, (d_u, sub_u), (x, drho2, I.id) :: vList, sList)
            end
      in
      findAllCands (g_r, children, ds, [], [])

    let divergingCtx (stage, g, gRlistRef) =
      let l = I.ctxLength g in
      List.exists
        (function
          | (evar, l), g', _, _, stage', _ ->
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
          | Some t1 -> eqTerm (t2, (t1, nid ()))
          end
      | I.Lam (d2, t2), (I.Lam (d, t_v), rho1) -> eqTerm (t2, (t_v, rho1))
      | _, (_, _) -> false

    and eqSpine = function
      | I.Nil, (I.Nil, rho1) -> true
      | I.App (t2, s2), (I.App (t_v, s), rho1) ->
          eqTerm (t2, (t_v, rho1)) && eqSpine (s2, (s, rho1))
      | _, _ -> false

    let divergingSub ((ds, sigma), (dr1, rho1), (dr2, rho2)) =
      S.exists rho2 (function n2, t2 ->
          S.exists sigma (function _, t -> eqTerm (t2, (t, rho1))))

    let rec insert (nref, (d_u, nsub_u), gr) =
      let insert' = function
        | ( (Leaf ((d, _), gRlistRef) as n),
            (d_u, nsub_u),
            (((evarl, l), g_r, eqn, answRef, stage, status) as gr) ) ->
            begin match compatibleCtx ((g_r, eqn), !gRlistRef) with
            | None ->
                begin if
                  !TableParam.divHeuristic
                  && divergingCtx (stage, g_r, gRlistRef)
                then function
                  | () ->
                      ( begin
                          gRlistRef := gr :: !gRlistRef;
                          answList := answRef :: !answList
                        end,
                        T.DivergingEntry (I.id, answRef) )
                else function
                  | () ->
                      ( begin
                          gRlistRef := gr :: !gRlistRef;
                          answList := answRef :: !answList
                        end,
                        T.NewEntry answRef )
                end
            | Some ((evarl', glength), answRef', status') -> (
                function
                | () -> ((), T.RepeatedEntry ((I.id, I.id), answRef', status')))
            end
        | ( (Node ((d, sub), children) as n),
            (d_u, nsub_u),
            ((l, g_r, eqn, answRef, stage, status) as gr) ) ->
            let variantCand, splitCand =
              findAllCandidates (g_r, children, (d_u, nsub_u))
            in
            let rec checkCandidates = function
              | [], [] -> (
                  function
                  | () ->
                      ( begin
                          nref :=
                            Node
                              ( (d, sub),
                                ref (Leaf ((d_u, nsub_u), ref [ gr ]))
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
                  begin match insert (childRef, drho2, gr) () with
                  | _, T.NewEntry answRef -> checkCandidates (l, sCands)
                  | f, T.RepeatedEntry (asub, answRef, status) ->
                      fun () -> (f, T.RepeatedEntry (asub, answRef, status))
                  | f, T.DivergingEntry (asub, answRef) ->
                      fun () -> (f, T.DivergingEntry (asub, answRef))
                  end
            in
            checkCandidates (variantCand, splitCand)
      in
      insert' (!nref, (d_u, nsub_u), gr)

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
      | I.Null, (dEVars : ctx) -> n
      | I.Decl (g, d), (dEVars : ctx) -> begin
          ignore (insertList ((n, d), dEVars));
          makeCtx (n + 1, g, dEVars)
        end

    let callCheck (a, dAVars, dEVars, g, u, eqn, status) =
      let n, tree = Array.sub (indexArray, a) in
      let nsub_goal = S.new_ () in
      let dAEVars = compose (dEVars, dAVars) in
      let d = emptyCtx () in
      let n = I.ctxLength g in
      ignore (makeCtx (n + 1, dAEVars, (d : ctx)));
      let l = I.ctxLength dAEVars in
      ignore (S.insert nsub_goal (1, u));
      let result =
        insert
          ( tree,
            (d, nsub_goal),
            ((l, n + 1), g, eqn, emptyAnswer (), !TableParam.stageCtr, status)
          )
      in
      let esub = ctxToAVarSub (g, dAEVars, I.Shift 0) in
      ignore begin if solveEqn' ((eqn, shift (g, esub)), g) then ()
        else print " failed to solve eqn_query\n"
        end;
      begin match result () with
      | _, T.NewEntry answRef -> begin
          begin
            added := true;
            begin
              Display.chatter_s 5 "\t -- Add goal \n";
              T.NewEntry answRef
            end
          end
        end
      | _, T.RepeatedEntry (((_, asub) as s), answRef, status) -> begin
          Display.chatter_s 5 "\t -- Suspend goal\n";
          T.RepeatedEntry ((esub, asub), answRef, status)
        end
      | _, T.DivergingEntry (_, answRef) -> begin
          begin
            added := true;
            begin
              Display.chatter_s 5 "\t -- Add diverging goal\n";
              T.DivergingEntry (I.id, answRef)
            end
          end
        end
      end

    let insertIntoTree (a, dAVars, dEVars, g, u, eqn, answRef, status) =
      let n, tree = Array.sub (indexArray, a) in
      let nsub_goal = S.new_ () in
      let dAEVars = compose (dEVars, dAVars) in
      let d = emptyCtx () in
      let n = I.ctxLength g in
      ignore (makeCtx (n + 1, dAEVars, (d : ctx)));
      let l = I.ctxLength dAEVars in
      ignore (S.insert nsub_goal (1, u));
      let result =
        insert
          ( tree,
            (d, nsub_goal),
            ((l, n + 1), g, eqn, answRef, !TableParam.stageCtr, status) )
      in
      begin match result () with
      | _, T.NewEntry answRef -> begin
          added := true;
          begin
            Display.chatter_s 5 "\t -- Add goal \n";
            T.NewEntry answRef
          end
        end
      | _, T.RepeatedEntry (asub, answRef, status) -> begin
          Display.chatter_s 5 "\t -- Suspend goal\n";
          T.RepeatedEntry (asub, answRef, status)
        end
      | _, T.DivergingEntry (_, answRef) -> begin
          begin
            added := true;
            begin
              Display.chatter_s 5 "\t -- Add diverging goal\n";
              T.DivergingEntry (I.id, answRef)
            end
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
  (* Auxiliary functions *)
  (* solveEqn' ((VarDef, s), G) = bool

     if G'' |- VarDef and G   |- s : G''
       G   |- VarDef[s]
    then
      return true, if VarDefs are solvable
      false otherwise
      *)
  (* evar *)
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

        linear terms are approximately well-typed in G:  G |- p
        after erasing all typing dependencies.


        Let s be a path in the substitution tree such that
        s1 o s2 o .... o sn = s,



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
      all expressions in the index are closed and linear, i.e.
      an expression is first linearized before it is inserted into the index
      (this makes retrieving all axpressions from the index which unify with
      a given expression simpler, because we can omit the occurs check)

   *)
  (* ---------------------------------------------------------------*)
  (* nctr = |D| =  #index variables *)
  (* We require order of both eqn must be the same Sun Sep  8 20:37:48 2002 -bp *)
  (* s = s' = I.id *)
  (* in general, we need to carry around and build up a substitution *)
  (* ---------------------------------------------------------------*)
  (* ---------------------------------------------------------------*)
  (* most specific linear common generalization *)
  (* compatible (t_v, U) = (t_v', rho_u, rho_t) opt
    if t_v is an indexed term
       U is a linear term
       U and t_v share at least the top function symbol
   then
       t_v'[rho_u] = U and t_v'[rho_t] = t_v
   *)
  (* globally bound variable *)
  (* k, k' refer to the existential *)
  (* they refer to the same existential variable *)
  (* this is unecessary -- since existential variables have the same type
                                and need to be fully applied in order, S1 = S2 *)
  (* variant checking only *)
  (* locally bound variables *)
  (* by invariant A1 = A2 *)
  (* U = EVar, EClo -- can't happen -- Sun Oct 20 13:41:25 2002 -bp *)
  (* ---------------------------------------------------------------*)
  (* compatibleSub(nsub_t, nsub_u) = (sigma, rho_t, rho_u) opt

   if DOM(nsub_t) <= DOM(nsub_u)
      CODOM(nsub_t) : index terms
      CODOM(nsub_u) : linear terms
        G_u, Glocal_u |- nsub_u
    N ; G_t, Glocal_t |- nsub_t
   then
     nsub_t = sigma o rho_t
     nsub_e = sigma o rho_u

    Glocal_e ~ Glocal_t  (have ""approximately"" the same type)

   *)
  (* by invariant rho_t = empty, since nsub_t <= nsub_u *)
  (* note by invariant Glocal_e ~ Glocal_t *)
  (* here Glocal_t will be only approximately correct! *)
  (* perfect match under asub and rho_t = nsub_t
           sigma = rho_t and sigma o asub = rho_u *)
  (* split -- asub is unchanged *)
  (* Dsigma |~ sigma, D_r1 |~ rho_t, D_r1 |~ rho_u *)
  (* ---------------------------------------------------------------------- *)
  (* ---------------------------------------------------------------------- *)
  (* we may not need to check that the DAVars are the same *)
  (* ---------------------------------------------------------------------- *)
  (* eqTerm (t2, (t, rho1)) = bool
    returns true iff t2 = t[rho1]
  t2 is a linear term which may not contain any nvars!
  t may contain nvars
 *)
  (* ---------------------------------------------------------------------- *)
  (* Insert via variant checking *)
  (* insert' (N, (D, nsub), GR) = (f, callCheckResult)

     invariant:

       N is a substitution tree
       nsub is a normal substitution
       D contains all the existential variables in nsub
       GR = (G : bound variable context,
             eqn: residual equations
             answRef : ptr to answer list

     if there exists a path p in N s.t. p ~ nsub
      then
       f is the identity, and callCheckResult = RepeatedEntry(_,_,answRef)
     otherwise (f is a function which destructively updates N
                and once executed, will add a path p ~ nsub to N,
                 callCheckResult = NewEntry (answRef)

  *)
  (* need to compare D and D_u *)
  (* compatible path -- but different ctx! *)
  (* ctx are diverging --- force suspension *)
  (* compatible path (variant) -- ctx are different *)
  (* compatible path -- SAME ctx *)
  (* no child is compatible with nsub_u *)
  (* split an existing node *)
  (* substree divering -- splitting node *)
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
  (* callCheck (a, DA, DE, G, U eqn) = callCheckResult

       invariant:
       DA, DE, G |- U
       a is the type family of U

       if U is not already in the index, then it is inserted.
       otherwise we return
             a pointer answRef to the answer list.
             (for variant checking, asub = I.id, and varDefs = NONE)
     *)
  (* insertIntoSTre (a, DA, DE, G, U eqn) = Succeeds

       invariant:
       DA, DE, G |- U
       a is the type family of U

       U is not already in the index, then it is inserted.
       otherwise we return
             a pointer answRef to the answer list.
             (for variant checking, asub = I.id, and varDefs = NONE)
     *)
  (* no new solutions were added in the previous stage *)
  (* new solutions were added *)
  let reset = reset

  let callCheck (dAVars, dEVars, g, u, eqn, status) =
        callCheck
          (cidFromHead (I.targetHead u), dAVars, dEVars, g, u, eqn, status)

  let insertIntoTree (dAVars, dEVars, g, u, eqn, answRef, status) =
        insertIntoTree
          ( cidFromHead (I.targetHead u),
            dAVars,
            dEVars,
            g,
            u,
            eqn,
            answRef,
            status )

  let answerCheck a b c = answCheck (a, b, c)
  let updateTable = updateTable
  let tableSize () = length !answList

  (* memberCtx ((G,V), G', n) = bool

       if G |- V and |- G' ctx
          exists a V' in G s.t. V = V'[^n]
       then return true
         otherwise false
     *)
  let memberCtx g v g' =
    let rec memberCtx' (a, b, n) = match a, b with
      | (g, v), I.Null -> None
      | (g, v), I.Decl (g', (I.Dec (_, v') as d')) ->
          begin if Conv.conv (v, I.id) (v', I.Shift n) then Some d'
          else memberCtx' ((g, v), g', n + 1)
          end
    in
    memberCtx' ((g, v), g', 1)
end
(*! sharing Print.IntSyn = IntSyn'!*)
(* local *)
(* functor MemoTable *)

(* # 1 "src/opsem/MemoTable.sml.ml" *)
