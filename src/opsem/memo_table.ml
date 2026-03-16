(* # 1 "src/opsem/memo_table.sig.ml" *)
open! Basis
open Table_param

(* Indexing *)
(* Author: Brigitte Pientka *)
module type MEMOTABLE = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  (*! structure TableParam : TABLEPARAM !*)
  (* call check/insert *)
  (* callCheck (G, D, U, eqn)
   *
   * if D, G |- U & eqn     in table  then RepeatedEntry (entries)
   * if D, G |- U & eqn not in table  then NewEntry (ptrAnswer)
   * SIDE EFFECT: D, G |- U added to table
   *)
  val callCheck :
    IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.exp
    * TableParam.resEqn
    * TableParam.status ->
    TableParam.callCheckResult

  (* answer check/insert *)
  (* answerCheck (G, D, (U,s))
   * 
   * Assupmtion: D, G |- U is in table
   *             and A represents the corresponding solutions
   * 
   * G |- s : D, G
   * Dk, G |- sk : D, G
   *
   * If  (Dk, sk) in A then repeated
   *  else new
   *)
  val answerCheck :
    IntSyn.sub * TableParam.answer * CompSyn.pskeleton -> TableParam.answState

  (* reset table *)
  val reset : unit -> unit

  (* updateTable 
   *
   * SIDE EFFECT: 
   *   for each table entry: 
   *       advance lookup pointer
   *
   * if Table did not change during last stage 
   *    then updateTable () =  false
   * else updateTable () = true
   *)
  val updateTable : unit -> bool
  val tableSize : unit -> int
  val memberCtx : (IntSyn.dctx * IntSyn.exp) * IntSyn.dctx -> IntSyn.dec option

  val insertIntoTree :
    IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.dctx
    * IntSyn.exp
    * TableParam.resEqn
    * TableParam.answer
    * TableParam.status ->
    TableParam.callCheckResult
end
(* signature MemoTable *)

(* # 1 "src/opsem/memo_table.fun.ml" *)
open! Basis
open Abstract_tabled
open Red_black_set

(* Linear Substitution Tree indexing *)
(* Linearity: Any variables occurring inside the substitution tree are linear *)
(* Any term we insert into the substitution tree is in normalform *)
(* Variant Checking *)
(* Author: Brigitte Pientka *)
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
  module AbstractTabled : Abstract_tabled.ABSTRACTTABLED

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
  let rec isId s = RBSet.isEmpty s

  (* ---------------------------------------------------------------------- *)
  type nonrec ctx = (int * IntSyn.dec) list ref

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
      | x, ((y, e_) :: l_ as h_) -> begin
          if x = y then Some (y, e_) else memb (x, l_)
        end
    in
    memb (x, !l_)

  let rec insertList (e_, l_) =
    begin
      l_ := e_ :: !l_;
      l_
    end

  (* ctxToEVarSub D = s

     if D is a context for existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)
  let rec ctxToEVarSub = function
    | I.Null, s -> s
    | IntSyn.Decl (g_, IntSyn.Dec (_, a_)), s ->
        let s' = ctxToEVarSub (g_, s) in
        let x_ = IntSyn.newEVar (IntSyn.Null, IntSyn.EClo (a_, s')) in
        IntSyn.Dot (IntSyn.Exp x_, s')

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

  let rec makeTree () = ref (Node ((emptyCtx (), nid ()), []))
  let rec noChildren c_ = c_ = []

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

  exception Error of string

  open! struct
    module I = IntSyn
    module C = CompSyn
    module S = RBSet
    module A = AbstractTabled
    module T = TableParam

    exception Assignment of string
    exception Generalization of string
    exception DifferentSpines

    let rec emptyAnswer () = T.emptyAnsw ()
    let answList : TableParam.answer list ref = ref []
    let added = ref false

    type nonrec nvar = int
    type nonrec bvar = int
    type nonrec bdepth = int

    let rec cidFromHead = function I.Const c -> c | I.Def c -> c
    let rec dotn = function 0, s -> s | i, s -> dotn (i - 1, I.dot1 s)

    let rec compose = function
      | I.Null, g_ -> g_
      | IntSyn.Decl (g_, d_), g'_ -> IntSyn.Decl (compose (g_, g'_), d_)

    let rec shift = function
      | I.Null, s -> s
      | IntSyn.Decl (g_, d_), s -> I.dot1 (shift (g_, s))

    let rec raiseType = function
      | I.Null, u_ -> u_
      | I.Decl (g_, d_), u_ -> raiseType (g_, I.Lam (d_, u_))

    let rec ctxToAVarSub = function
      | g'_, I.Null, s -> s
      | g'_, I.Decl (d_, I.Dec (_, a_)), s ->
          let (I.EVar (r, _, _, cnstr) as e_) = I.newEVar (I.Null, a_) in
          I.Dot (I.Exp e_, ctxToAVarSub (g'_, d_, s))
      | g'_, I.Decl (d_, I.ADec (_, d)), s ->
          let x_ = I.newAVar () in
          I.Dot (I.Exp (I.EClo (x_, I.Shift (-d))), ctxToAVarSub (g'_, d_, s))

    let rec solveEqn' = function
      | (trivial_, s), g_ -> true
      | (T.Unify (g'_, e1, n_, eqns), s), g_ ->
          let g''_ = compose (g'_, g_) in
          let s' = shift (g'_, s) in
          Assign__.unifiable (g''_, (n_, s'), (e1, s'))
          && solveEqn' ((eqns, s), g_)

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
      | I.Decl (g_, d_), s, I.Decl (g'_, d'_), s' ->
          Conv.convDec ((d_, s), (d'_, s'))
          && equalCtx (g_, I.dot1 s, g'_, I.dot1 s')
      | _, _, _, _ -> false

    let rec equalEqn = function
      | T.Trivial, T.Trivial -> true
      | T.Unify (g_, x_, n_, eqn), T.Unify (g'_, x'_, n'_, eqn') ->
          equalCtx (g_, I.id, g'_, I.id)
          && Conv.conv ((x_, I.id), (x'_, I.id))
          && Conv.conv ((n_, I.id), (n'_, I.id))
          && equalEqn (eqn, eqn')
      | _, _ -> false

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

    let rec equalSub1 (I.Dot (ms, s), I.Dot (ms', s')) = equalSub (s, s')

    let rec equalCtx' = function
      | I.Null, I.Null -> true
      | I.Decl (dk_, I.Dec (_, a_)), I.Decl (d1_, I.Dec (_, a1_)) ->
          Conv.conv ((a_, I.id), (a1_, I.id)) && equalCtx' (dk_, d1_)
      | I.Decl (dk_, I.ADec (_, d')), I.Decl (d1_, I.ADec (_, d)) ->
          d = d' && equalCtx' (dk_, d1_)
      | _, _ -> false

    let rec compareCtx (g_, g'_) = equalCtx' (g_, g'_)
    let rec isExists (d, I.BVar k, d_) = member (k - d, d_)

    let rec compHeads = function
      | (d_1_, I.Const k), (d_2_, I.Const k') -> k = k'
      | (d_1_, I.Def k), (d_2_, I.Def k') -> k = k'
      | (d_1_, I.BVar k), (d_2_, I.BVar k') -> begin
          match isExists (0, I.BVar k, d_1_) with
          | None -> k = k'
          | Some (x, _dec) -> true
        end
      | (d_1_, I.BVar k), (d_2_, h2_) -> begin
          match isExists (0, I.BVar k, d_1_) with
          | None -> false
          | Some (x, _dec) -> true
        end
      | (d_1_, h1_), (d_2_, h2_) -> false

    let rec compatible' ((d_t_, t_v), (d_u_, u_), ds_, rho_t, rho_u) =
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
        | ( depth,
            (I.Root ((I.Const k as h1_), s1_) as t_),
            (I.Root (I.Const k', s2_) as u_) ) -> begin
            if k = k' then
              let s'_ = genSpine (depth, s1_, s2_) in
              I.Root (h1_, s'_)
            else genNVar ((rho_t, t_v), (rho_u, u_))
          end
        | ( depth,
            (I.Root ((I.Def k as h1_), s1_) as t_),
            (I.Root (I.Def k', s2_) as u_) ) -> begin
            if k = k' then
              let s'_ = genSpine (depth, s1_, s2_) in
              I.Root (h1_, s'_)
            else genNVar ((rho_t, t_v), (rho_u, u_))
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
                    with differentSpine_ -> genNVar ((rho_t, t_v), (rho_u, u_))
                  else genNVar ((rho_t, t_v), (rho_u, u_))
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
                  else genNVar ((rho_t, t_v), (rho_u, u_))
                end
              | _, _ -> genNVar ((rho_t, t_v), (rho_u, u_))
              end
            else begin
              if k = k' then
                try
                  let s'_ = genSpine (d, s1_, s2_) in
                  I.Root (h1_, s'_)
                with DifferentSpines -> genNVar ((rho_t, t_v), (rho_u, u_))
              else genNVar ((rho_t, t_v), (rho_u, u_))
            end
          end
        | ( d,
            (I.Root ((I.BVar k as h1_), s1_) as t_),
            (I.Root (I.Const k', s2_) as u_) ) ->
            genNVar ((rho_t, t_v), (rho_u, u_))
        | d, (I.Root (h1_, s1_) as t_), (I.Root (h2_, s2_) as u_) ->
            genNVar ((rho_t, t_v), (rho_u, u_))
      and genExp = function
        | d, (I.NVar n as t_), (I.Root (h_, s_) as u_) -> begin
            S.insert rho_u (n, u_);
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
            genNVar ((rho_t, t_v), (rho_u, u_))
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
      let e_ = genExp (0, t_v, u_) in
      Variant e_

    let rec compatible = function
      | ( (d_t_, (I.Root (h1_, s1_) as t_)),
          (d_u_, (I.Root (h2_, s2_) as u_)),
          ds_,
          rho_t,
          rho_u ) -> begin
          if compHeads ((d_t_, h1_), (d_u_, h2_)) then
            compatible' ((d_t_, t_), (d_u_, u_), ds_, rho_t, rho_u)
          else NotCompatible
        end
      | (d_t_, t_v), (d_u_, u_), ds_, rho_t, rho_u ->
          compatible' ((d_t_, t_v), (d_u_, u_), ds_, rho_t, rho_u)

    let rec compatibleSub ((d_t_, nsub_t), (d_u_, nsub_u)) =
      let sigma, rho_t, rho_u = (nid (), nid (), nid ()) in
      let dsigma_ = emptyCtx () in
      let d_r1_ = copy d_t_ in
      let d_r2_ = copy d_u_ in
      let choose = ref (function (match_ : bool) -> ()) in
      let _ =
        S.forall nsub_u (function nv, u_ ->
            begin match S.lookup nsub_t nv with
            | Some t_v -> begin
                match
                  compatible ((d_r1_, t_v), (d_r2_, u_), dsigma_, rho_t, rho_u)
                with
                | NotCompatible -> begin
                    S.insert rho_t (nv, t_v);
                    S.insert rho_u (nv, u_)
                  end
                | Variant t'_ ->
                    let restc = !choose in
                    begin
                      S.insert sigma (nv, t'_);
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

    let rec mkLeaf (ds_, gr_, n) = Leaf (ds_, gr_)

    let rec mkNode = function
      | Node (_, children_), dsigma_, drho1_, gr_, drho2_ ->
          Node
            ( dsigma_,
              [
                ref (Leaf (drho2_, ref [ gr_ ])); ref (Node (drho1_, children_));
              ] )
      | Leaf (c, gRlist_), dsigma_, drho1_, gr2_, drho2_ ->
          Node
            ( dsigma_,
              [
                ref (Leaf (drho2_, ref [ gr2_ ])); ref (Leaf (drho1_, gRlist_));
              ] )

    let rec compatibleCtx = function
      | (g_, eqn), [] -> None
      | (g_, eqn), (l', g'_, eqn', answRef', _, status') :: gRlist_ -> begin
          if equalCtx' (g_, g'_) && equalEqn (eqn, eqn') then
            Some (l', answRef', status')
          else compatibleCtx ((g_, eqn), gRlist_)
        end

    let rec compChild = function
      | (Leaf ((d_t_, nsub_t), gList_) as n_), (d_e_, nsub_e) ->
          compatibleSub ((d_t_, nsub_t), (d_e_, nsub_e))
      | (Node ((d_t_, nsub_t), children'_) as n_), (d_e_, nsub_e) ->
          compatibleSub ((d_t_, nsub_t), (d_e_, nsub_e))

    let rec findAllCandidates (g_r_, children, ds_) =
      let rec findAllCands = function
        | g_r_, [], (d_u_, sub_u), vList_, sList_ -> (vList_, sList_)
        | g_r_, x :: l_, (d_u_, sub_u), vList_, sList_ -> begin
            match compChild (!x, (d_u_, sub_u)) with
            | NoCompatibleSub ->
                findAllCands (g_r_, l_, (d_u_, sub_u), vList_, sList_)
            | SplitSub (dsigma_, drho1_, drho2_) ->
                findAllCands
                  ( g_r_,
                    l_,
                    (d_u_, sub_u),
                    vList_,
                    (x, (dsigma_, drho1_, drho2_)) :: sList_ )
            | VariantSub (d_r2_, rho2) ->
                let drho2_ = (d_r2_, rho2) in
                findAllCands
                  (g_r_, l_, (d_u_, sub_u), (x, drho2_, I.id) :: vList_, sList_)
          end
      in
      findAllCands (g_r_, children, ds_, [], [])

    let rec divergingCtx (stage, g_, gRlistRef_) =
      let l = I.ctxLength g_ in
      List.exists
        (function
          | (evar_, l), g'_, _, _, stage', _ ->
              stage = stage' && l > I.ctxLength g'_)
        !gRlistRef_

    let rec eqHeads = function
      | I.Const k, I.Const k' -> k = k'
      | I.BVar k, I.BVar k' -> k = k'
      | I.Def k, I.Def k' -> k = k'
      | _, _ -> false

    let rec eqTerm = function
      | I.Root (h2_, s2_), ((I.Root (h_, s_) as t), rho1) -> begin
          if eqHeads (h2_, h_) then eqSpine (s2_, (s_, rho1)) else false
        end
      | t2_, (I.NVar n, rho1) -> begin
          match S.lookup rho1 n with
          | None -> false
          | Some t1_ -> eqTerm (t2_, (t1_, nid ()))
        end
      | I.Lam (d2_, t2_), (I.Lam (d_, t_v), rho1) -> eqTerm (t2_, (t_v, rho1))
      | _, (_, _) -> false

    and eqSpine = function
      | I.Nil, (I.Nil, rho1) -> true
      | I.App (t2_, s2_), (I.App (t_v, s_), rho1) ->
          eqTerm (t2_, (t_v, rho1)) && eqSpine (s2_, (s_, rho1))
      | _, _ -> false

    let rec divergingSub ((ds_, sigma), (dr1_, rho1), (dr2_, rho2)) =
      S.exists rho2 (function n2, t2 ->
          S.exists sigma (function _, t -> eqTerm (t2, (t, rho1))))

    let rec insert (nref_, (d_u_, nsub_u), gr_) =
      let rec insert' = function
        | ( (Leaf ((d_, _), gRlistRef_) as n_),
            (d_u_, nsub_u),
            (((evarl, l), g_r_, eqn, answRef, stage, status) as gr_) ) -> begin
            match compatibleCtx ((g_r_, eqn), !gRlistRef_) with
            | None -> begin
                if
                  !TableParam.divHeuristic
                  && divergingCtx (stage, g_r_, gRlistRef_)
                then function
                  | () ->
                      ( begin
                          gRlistRef_ := gr_ :: !gRlistRef_;
                          answList := answRef :: !answList
                        end,
                        T.DivergingEntry (I.id, answRef) )
                else function
                  | () ->
                      ( begin
                          gRlistRef_ := gr_ :: !gRlistRef_;
                          answList := answRef :: !answList
                        end,
                        T.NewEntry answRef )
              end
            | Some ((evarl', glength_), answRef', status') -> (
                function
                | () -> ((), T.RepeatedEntry ((I.id, I.id), answRef', status')))
          end
        | ( (Node ((d_, sub), children) as n_),
            (d_u_, nsub_u),
            ((l, g_r_, eqn, answRef, stage, status) as gr_) ) ->
            let variantCand_, splitCand_ =
              findAllCandidates (g_r_, children, (d_u_, nsub_u))
            in
            let rec checkCandidates = function
              | [], [] -> (
                  function
                  | () ->
                      ( begin
                          nref_ :=
                            Node
                              ( (d_, sub),
                                ref (Leaf ((d_u_, nsub_u), ref [ gr_ ]))
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
                  match insert (childRef_, drho2_, gr_) () with
                  | _, T.NewEntry answRef -> checkCandidates (l_, sCands_)
                  | f, T.RepeatedEntry (asub, answRef, status) ->
                      fun () -> (f, T.RepeatedEntry (asub, answRef, status))
                  | f, T.DivergingEntry (asub, answRef) ->
                      fun () -> (f, T.DivergingEntry (asub, answRef))
                end
            in
            checkCandidates (variantCand_, splitCand_)
      in
      insert' (!nref_, (d_u_, nsub_u), gr_)

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
      | n, I.Null, (dEVars_ : ctx) -> n
      | n, I.Decl (g_, d_), (dEVars_ : ctx) -> begin
          ignore (insertList ((n, d_), dEVars_));
          makeCtx (n + 1, g_, dEVars_)
        end

    let rec callCheck (a, dAVars_, dEVars_, g_, u_, eqn, status) =
      let n, tree = Array.sub (indexArray, a) in
      let nsub_goal = S.new_ () in
      let dAEVars_ = compose (dEVars_, dAVars_) in
      let d_ = emptyCtx () in
      let n = I.ctxLength g_ in
      let _ = makeCtx (n + 1, dAEVars_, (d_ : ctx)) in
      let l = I.ctxLength dAEVars_ in
      let _ = S.insert nsub_goal (1, u_) in
      let result =
        insert
          ( tree,
            (d_, nsub_goal),
            ((l, n + 1), g_, eqn, emptyAnswer (), !TableParam.stageCtr, status)
          )
      in
      let esub = ctxToAVarSub (g_, dAEVars_, I.Shift 0) in
      let _ =
        begin if solveEqn' ((eqn, shift (g_, esub)), g_) then ()
        else print " failed to solve eqn_query\n"
        end
      in
      begin match result () with
      | _, T.NewEntry answRef -> begin
          begin
            added := true;
            begin
              begin if !Global.chatter >= 5 then print "\t -- Add goal \n"
              else ()
              end;
              T.NewEntry answRef
            end
          end
        end
      | _, T.RepeatedEntry (((_, asub) as s), answRef, status) -> begin
          begin if !Global.chatter >= 5 then print "\t -- Suspend goal\n"
          else ()
          end;
          T.RepeatedEntry ((esub, asub), answRef, status)
        end
      | _, T.DivergingEntry (_, answRef) -> begin
          begin
            added := true;
            begin
              begin if !Global.chatter >= 5 then
                print "\t -- Add diverging goal\n"
              else ()
              end;
              T.DivergingEntry (I.id, answRef)
            end
          end
        end
      end

    let rec insertIntoTree (a, dAVars_, dEVars_, g_, u_, eqn, answRef, status) =
      let n, tree = Array.sub (indexArray, a) in
      let nsub_goal = S.new_ () in
      let dAEVars_ = compose (dEVars_, dAVars_) in
      let d_ = emptyCtx () in
      let n = I.ctxLength g_ in
      let _ = makeCtx (n + 1, dAEVars_, (d_ : ctx)) in
      let l = I.ctxLength dAEVars_ in
      let _ = S.insert nsub_goal (1, u_) in
      let result =
        insert
          ( tree,
            (d_, nsub_goal),
            ((l, n + 1), g_, eqn, answRef, !TableParam.stageCtr, status) )
      in
      begin match result () with
      | _, T.NewEntry answRef -> begin
          added := true;
          begin
            begin if !Global.chatter >= 5 then print "\t -- Add goal \n" else ()
            end;
            T.NewEntry answRef
          end
        end
      | _, T.RepeatedEntry (asub, answRef, status) -> begin
          begin if !Global.chatter >= 5 then print "\t -- Suspend goal\n"
          else ()
          end;
          T.RepeatedEntry (asub, answRef, status)
        end
      | _, T.DivergingEntry (_, answRef) -> begin
          begin
            added := true;
            begin
              begin if !Global.chatter >= 5 then
                print "\t -- Add diverging goal\n"
              else ()
              end;
              T.DivergingEntry (I.id, answRef)
            end
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
  let tableSize = function () -> length !answList

  (* memberCtx ((G,V), G', n) = bool

       if G |- V and |- G' ctx
          exists a V' in G s.t. V = V'[^n]
       then return true
         otherwise false
     *)
  let rec memberCtx ((g_, v_), g'_) =
    let rec memberCtx' = function
      | (g_, v_), I.Null, n -> None
      | (g_, v_), I.Decl (g'_, (I.Dec (_, v'_) as d'_)), n -> begin
          if Conv.conv ((v_, I.id), (v'_, I.Shift n)) then Some d'_
          else memberCtx' ((g_, v_), g'_, n + 1)
        end
    in
    memberCtx' ((g_, v_), g'_, 1)
end
(*! sharing Print.IntSyn = IntSyn'!*)
(* local *)
(* functor MemoTable *)

(* # 1 "src/opsem/memo_table.sml.ml" *)
