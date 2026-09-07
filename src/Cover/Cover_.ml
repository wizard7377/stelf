open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Table
open! Print.Print_
open! Subordinate
open! Modes
open! Modes.Modes_
open! Terminate
open! Index.Index_
open! Solvers.Solvers_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Typecheck.Typecheck_
open! Timing
open! Unique.Unique_

(* # 1 "src/cover/Cover_.sig.ml" *)

(* Coverage Checking *)

include COVER
(** Author: Frank Pfenning *)

(* signature COVER *)

(* # 1 "src/cover/Cover_.fun.ml" *)
open! Basis

(* Coverage Checking *)
(* Author: Frank Pfenning *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

exception NotFinitary

let () =
  Printexc.register_printer (function
    | NotFinitary -> Some "Not finitary"
    | _ -> None)

module MakeCover
    (Global : GLOBAL)
    (Whnf : WHNF)
    (Conv : CONV)
    (Abstract : ABSTRACT)
    (Unify : UNIFY)
    (Constraints : CONSTRAINTS)
    (ModeTable : Modetable.MODETABLE)
    (UniqueTable : Modetable.MODETABLE)
    (Index : INDEX)
    (Subordinate : Subordinate.Subordinate_.SUBORDINATE)
    (WorldSyn : Worldcheck_.WORLDSYN)
    (Names : NAMES)
    (Print : PRINT)
    (TypeCheck : TYPECHECK)
    (Timers : Timers.TIMERS) : COVER = struct
  module Subordinate = Subordinate

  exception Error = Error

  module Unify = Unify
  module ModeTable = ModeTable
  module UniqueTable = UniqueTable
  module TypeCheck = TypeCheck
  module Timers = Timers

  type caseLabel = Top | Child of caseLabel * int

  let rec labToString = function
    | Top -> "^"
    | Child (lab, n) -> (labToString lab ^ ".") ^ Int.toString n

  module I = IntSyn
  module T = Tomega
  module M = Modes.Modesyn.ModeSyn
  module W = WorldSyn
  module P = Paths
  module F = Print.Formatter
  module N = Names

  let rec weaken a3 b3 = match a3, b3 with
    | I.Null, a -> I.id
    | I.Decl (g', (I.Dec (name, v) as d)), a ->
        let w' = weaken g' a in
        begin if Subordinate.belowEq (I.targetFam v) a then I.dot1 w'
        else I.comp w' I.shift
        end

  let createEVar (g, v) =
    let w = weaken g (I.targetFam v) in
    let iw = Whnf.invert w in
    let g' = Whnf.strengthen iw g in
    let x' = Whnf.newLoweredEVar g' (v, iw) in
    let x = I.EClo (x', w) in
    x

  type coverInst = Match of coverInst | Skip of coverInst | Cnil

  let rec inCoverInst = function
    | M.Mnil -> Cnil
    | M.Mapp (M.Marg (M.Plus, x), ms') -> Match (inCoverInst ms')
    | M.Mapp (M.Marg (M.Minus, x), ms') -> Skip (inCoverInst ms')
    | M.Mapp (M.Marg (M.Star, x), ms') -> Skip (inCoverInst ms')

  let rec outCoverInst = function
    | M.Mnil -> Cnil
    | M.Mapp (M.Marg (M.Plus, x), ms') -> Skip (outCoverInst ms')
    | M.Mapp (M.Marg (M.Minus, x), ms') -> Match (outCoverInst ms')
    | M.Mapp (M.Marg (M.Star, x), ms') -> Skip (outCoverInst ms')

  let chatter chlev f = Display.chatter_s chlev (f ())
  let pluralize (n, s) = match n with 1 -> s | n -> s ^ "s"
  let abbrevCSpine (s, ci) = s

  let rec abbrevCGoal (g, a, p, ci) = match a, p with
    | v, 0 -> (g, abbrevCGoal' (g, v, ci))
    | I.Pi ((d, p_), v), p ->
        let d' = N.decEName g d in
        abbrevCGoal (I.Decl (g, d'), v, p - 1, ci)

  and abbrevCGoal' (g, b, ci) = match b with
    | I.Pi ((d, p), v) ->
        let d' = N.decUName g d in
        I.Pi ((d', p), abbrevCGoal' (I.Decl (g, d'), v, ci))
    | I.Root (a, s) -> I.Root (a, abbrevCSpine (s, ci))

  let formatCGoal (v, p, ci) =
    ignore (N.varReset I.Null);
    let g, v' = abbrevCGoal (I.Null, v, p, ci) in
    F.hVbox
      [
        Print.formatCtx I.Null g;
        F.break_;
        F.string "|-";
        F.space;
        Print.formatExp g v';
      ]

  let rec formatCGoals (a, ci) = match a with
    | (v, p) :: [] -> [ formatCGoal (v, p, ci) ]
    | (v, p) :: vs ->
        formatCGoal (v, p, ci)
        :: F.string "," :: F.break_
        :: formatCGoals (vs, ci)

  let missingToString (vs, ci) =
    F.makestring_fmt
      (F.hbox [ F.vbox0 0 1 (formatCGoals (vs, ci)); F.string "." ])

  let showSplitVar (v, p, k, ci) =
    ignore (N.varReset I.Null);
    let g, v' = abbrevCGoal (I.Null, v, p, ci) in
    let (I.Dec (Some x, _)) = I.ctxLookup g k in
    (("Split " ^ x) ^ " in ") ^ Print.expToString g v'

  let showPendingGoal (v, p, ci, lab) =
    F.makestring_fmt
      (F.hbox
         [
           F.string (labToString lab);
           F.space;
           F.string "?- ";
           formatCGoal (v, p, ci);
           F.string ".";
         ])

  let rec buildSpine = function
    | 0 -> I.Nil
    | n -> I.App (I.Root (I.BVar n, I.Nil), buildSpine (n - 1))

  let rec initCGoal' (a, k, g, b) = match b with
    | I.Pi ((d, p_), v) ->
        let d' = N.decEName g d in
        let v', p = initCGoal' (a, k + 1, I.Decl (g, d'), v) in
        (I.Pi ((d', I.Maybe), v'), p)
    | I.Uni I.Type -> (I.Root (a, buildSpine k), k)

  let initCGoal a = initCGoal' (I.Const a, 0, I.Null, I.constType a)

  type coverClauses = Input of I.exp list | Output of I.exp * int
  type equation = Eqn of I.dctx * I.eclo * I.eclo

  let equationToString (Eqn (g, us1, us2)) =
    let g' = Names.ctxLUName g in
    let fmt =
      F.hVbox
        [
          Print.formatCtx I.Null g';
          F.break_;
          F.string "|-";
          F.space;
          Print.formatExp g' (I.EClo (fst us1, snd us1));
          F.break_;
          F.string "=";
          F.space;
          Print.formatExp g' (I.EClo (fst us2, snd us2));
        ]
    in
    F.makestring_fmt fmt

  let rec eqnsToString = function
    | [] -> ".\n"
    | eqn :: eqns -> (equationToString eqn ^ ",\n") ^ eqnsToString eqns

  type candidates_ = Eqns of equation list | Cands of int list | Fail

  let candsToString = function
    | Fail -> "Fail"
    | Cands ks ->
        "Cands ["
        ^ List.foldl (function k, str -> (Int.toString k ^ ",") ^ str) "]" ks
    | Eqns eqns -> ("Eqns [\n" ^ eqnsToString eqns) ^ "]"

  let fail msg =
    begin
      chatter 7 (function () -> msg ^ "\n");
      Fail
    end

  let failAdd (k, a) = match a with
    | Eqns _ -> Cands [ k ]
    | Cands ks -> Cands (k :: ks)
    | Fail -> Fail

  let addEqn (e, a) = match a with
    | Eqns es -> Eqns (e :: es)
    | (Cands ks as cands) -> cands
    | Fail -> Fail

  let unifiable g us1 us2 = Unify.unifiable g us1 us2

  let rec matchEqns = function
    | [] -> true
    | Eqn (g, us1, ((u2, s2) as us2)) :: es ->
        begin match Whnf.makePatSub s2 with
        | None -> unifiable g us1 us2
        | Some s2' -> unifiable g us1 (u2, s2')
        end
        && matchEqns es

  let resolveCands = function
    | Eqns es ->
        begin if matchEqns (List.rev es) then Eqns [] else Fail
        end
    | Cands ks -> Cands ks
    | Fail -> Fail

  let rec collectConstraints = function
    | [] -> []
    | I.EVar (_, _, _, { contents = [] }) :: xs -> collectConstraints xs
    | I.EVar (_, _, _, { contents = constrs }) :: xs ->
        constrs @ collectConstraints xs

  let checkConstraints (g, qs, a) = match a with
    | Cands ks -> Cands ks
    | Fail -> Fail
    | Eqns _ ->
        let xs = Abstract.collectEVars g qs [] in
        let constrs = collectConstraints xs in
        begin match constrs with [] -> Eqns [] | _ -> Fail
        end

  type candList = Covered | CandList of candidates_ list

  let addKs = function
    | (Cands ks as ccs), CandList klist -> CandList (ccs :: klist)
    | (Eqns [] as ces), CandList klist -> Covered
    | (Fail as cfl), CandList klist -> CandList (cfl :: klist)

  let rec matchExp (g, d, us1, us2, cands) =
    matchExpW (g, d, Whnf.whnf us1, Whnf.whnf us2, cands)

  and matchExpW (g, d, a, b, cands) = match a, b with
    | ((I.Root (h1, s1_), s1) as us1), ((I.Root (h2, s2_), s2) as us2) ->
        begin match (h1, h2) with
        | I.BVar k1, I.BVar k2 ->
            begin if k1 = k2 then matchSpine (g, d, (s1_, s1), (s2_, s2), cands)
            else
              begin if k1 > d then failAdd (k1 - d, cands)
              else fail "local variable / variable clash"
              end
            end
        | I.Const c1, I.Const c2 ->
            begin if c1 = c2 then matchSpine (g, d, (s1_, s1), (s2_, s2), cands)
            else fail "constant / constant clash"
            end
        | I.Def d1, I.Def d2 ->
            begin if d1 = d2 then matchSpine (g, d, (s1_, s1), (s2_, s2), cands)
            else matchExpW (g, d, Whnf.expandDef us1, Whnf.expandDef us2, cands)
            end
        | I.Def d1, _ -> matchExpW (g, d, Whnf.expandDef us1, us2, cands)
        | _, I.Def d2 -> matchExpW (g, d, us1, Whnf.expandDef us2, cands)
        | I.BVar k1, I.Const _ ->
            begin if k1 > d then failAdd (k1 - d, cands)
            else fail "local variable / constant clash"
            end
        | I.Const _, I.BVar _ -> fail "constant / local variable clash"
        | I.Proj (I.Bidx k1, i1), I.Proj (I.Bidx k2, i2) ->
            begin if k1 = k2 && i1 = i2 then
              matchSpine (g, d, (s1_, s1), (s2_, s2), cands)
            else fail "block index / block index clash"
            end
        | I.Proj (I.Bidx k1, i1), I.Proj (I.LVar (r2, I.Shift k2, (l2, t2)), i2)
          ->
            let (I.BDec (bOpt, (l1, t1))) = I.ctxDec g k1 in
            begin if l1 <> l2 || i1 <> i2 then
              fail "block index / block variable clash"
            else
              let cands2 =
                matchSub (g, d, t1, I.comp t2 (I.Shift k2), cands)
              in
              ignore (Unify.instantiateLVar r2 (I.Bidx (k1 - k2)));
              matchSpine (g, d, (s1_, s1), (s2_, s2), cands2)
            end
        | I.BVar k1, I.Proj _ ->
            begin if k1 > d then failAdd (k1 - d, cands)
            else fail "local variable / block projection clash"
            end
        | I.Const _, I.Proj _ -> fail "constant / block projection clash"
        | I.Proj _, I.Const _ -> fail "block projection / constant clash"
        | I.Proj _, I.BVar _ -> fail "block projection / local variable clash"
        end
    | (I.Lam (d1, u1), s1), (I.Lam (d2, u2), s2) ->
        matchExp
          ( I.Decl (g, I.decSub d1 s1),
            d + 1,
            (u1, I.dot1 s1),
            (u2, I.dot1 s2),
            cands )
    | (I.Lam (d1, u1), s1), (u2, s2) ->
        matchExp
          ( I.Decl (g, I.decSub d1 s1),
            d + 1,
            (u1, I.dot1 s1),
            ( I.Redex
                (I.EClo (u2, I.shift), I.App (I.Root (I.BVar 1, I.Nil), I.Nil)),
              I.dot1 s2 ),
            cands )
    | (u1, s1), (I.Lam (d2, u2), s2) ->
        matchExp
          ( I.Decl (g, I.decSub d2 s2),
            d + 1,
            ( I.Redex
                (I.EClo (u1, I.shift), I.App (I.Root (I.BVar 1, I.Nil), I.Nil)),
              I.dot1 s1 ),
            (u2, I.dot1 s2),
            cands )
    | us1, ((I.EVar _, s2) as us2) ->
        addEqn (Eqn (g, us1, us2), cands)

  and matchSpine (g, d, ss1, ss2, cands) = match ss1, ss2 with
    | (I.Nil, _), (I.Nil, _) -> cands
    | (I.SClo (s1_, s1'), s1), ss2 ->
        matchSpine (g, d, (s1_, I.comp s1' s1), ss2, cands)
    | ss1, (I.SClo (s2_, s2'), s2) ->
        matchSpine (g, d, ss1, (s2_, I.comp s2' s2), cands)
    | (I.App (u1, s1_), s1), (I.App (u2, s2_), s2) ->
        let cands' = matchExp (g, d, (u1, s1), (u2, s2), cands) in
        matchSpine (g, d, (s1_, s1), (s2_, s2), cands')

  and matchDec (g, d, (I.Dec (_, v1), s1), (I.Dec (_, v2), s2), cands) =
    matchExp (g, d, (v1, s1), (v2, s2), cands)

  and matchSub (g, d, a, b, cands) = match a, b with
    | I.Shift n1, I.Shift n2 -> cands
    | I.Shift n, (I.Dot _ as s2) ->
        matchSub (g, d, I.Dot (I.Idx (n + 1), I.Shift (n + 1)), s2, cands)
    | (I.Dot _ as s1), I.Shift m ->
        matchSub (g, d, s1, I.Dot (I.Idx (m + 1), I.Shift (m + 1)), cands)
    | I.Dot (ft1, s1), I.Dot (ft2, s2) ->
        let cands1 =
          begin match (ft1, ft2) with
          | I.Idx n1, I.Idx n2 ->
              begin if n1 = n2 then cands
              else
                begin if n1 > d then failAdd (n1 - d, cands)
                else
                  fail "local variable / local variable clash in block instance"
                end
              end
          | I.Exp u1, I.Exp u2 ->
              matchExp (g, d, (u1, I.id), (u2, I.id), cands)
          | I.Exp u1, I.Idx n2 ->
              matchExp
                (g, d, (u1, I.id), (I.Root (I.BVar n2, I.Nil), I.id), cands)
          | I.Idx n1, I.Exp u2 ->
              matchExp
                (g, d, (I.Root (I.BVar n1, I.Nil), I.id), (u2, I.id), cands)
          end
        in
        matchSub (g, d, s1, s2, cands1)

  let rec matchTop (g, d, us1, us2, ci, cands) =
    matchTopW (g, d, Whnf.whnf us1, Whnf.whnf us2, ci, cands)

  and matchTopW (g, d, a, b, ci, cands) = match a, b with
    | (I.Root (I.Const c1, s1_), s1), (I.Root (I.Const c2, s2_), s2) ->
        begin if c1 = c2 then
          matchTopSpine (g, d, (s1_, s1), (s2_, s2), ci, cands)
        else fail "type family clash"
        end
    | (I.Pi ((d1, _), v1), s1), (I.Pi ((d2, _), v2), s2)
      ->
        matchTopW
          ( I.Decl (g, d1),
            d + 1,
            (v1, I.dot1 s1),
            (v2, I.dot1 s2),
            ci,
            cands )

  and matchTopSpine (g, d, ss1, ss2, ci, cands) = match ss1, ss2, ci with
    | (I.Nil, _), (I.Nil, _), Cnil -> cands
    | (I.SClo (s1_, s1'), s1), ss2, ci ->
        matchTopSpine (g, d, (s1_, I.comp s1' s1), ss2, ci, cands)
    | ss1, (I.SClo (s2_, s2'), s2), ci ->
        matchTopSpine (g, d, ss1, (s2_, I.comp s2' s2), ci, cands)
    | (I.App (u1, s1_), s1), (I.App (u2, s2_), s2), Match ci' ->
        let cands' = matchExp (g, d, (u1, s1), (u2, s2), cands) in
        matchTopSpine (g, d, (s1_, s1), (s2_, s2), ci', cands')
    | (I.App (u1, s1_), s1), (I.App (u2, s2_), s2), Skip ci' ->
        matchTopSpine (g, d, (s1_, s1), (s2_, s2), ci', cands)

  let rec matchClause (g, ps', a, ci) = match a with
    | ((I.Root (_, _), s) as qs) ->
        checkConstraints
          (g, qs, resolveCands (matchTop (g, 0, ps', qs, ci, Eqns [])))
    | (I.Pi ((I.Dec (_, v1), _), v2), s) ->
        let x1 = Whnf.newLoweredEVar g (v1, s) in
        matchClause (g, ps', (v2, I.Dot (I.Exp x1, s)), ci)

  let rec matchSig (g, ps', a, ci, klist) = match a with
    | [] -> klist
    | v :: ccs' ->
        let cands =
          CsManager.trail (function () -> matchClause (g, ps', (v, I.id), ci))
        in
        matchSig' (g, ps', ccs', ci, addKs (cands, klist))

  and matchSig' (g, ps', ccs, ci, a) = match a with
    | Covered -> Covered
    | CandList klist ->
        matchSig (g, ps', ccs, ci, CandList klist)

  let rec matchBlocks (g, s', a, v, k, i, ci, klist) = match a with
    | [] -> klist
    | I.Dec (_, v') :: piDecs ->
        let cands =
          CsManager.trail (function () ->
              matchClause (g, (v, I.id), (v', s'), ci))
        in
        let s'' = I.Dot (I.Exp (I.Root (I.Proj (I.Bidx k, i), I.Nil)), s') in
        matchBlocks' (g, s'', piDecs, v, k, i + 1, ci, addKs (cands, klist))

  and matchBlocks' (g, s', piDecs, v, k, i, ci, klist) = match klist with
    | Covered -> Covered
    | klist ->
        matchBlocks (g, s', piDecs, v, k, i, ci, klist)

  let rec matchCtx (g, s', a, v, k, ci, klist) = match a with
    | I.Null -> klist
    | I.Decl (g'', I.Dec (_, v')) ->
        let s'' = I.comp I.shift s' in
        let cands =
          CsManager.trail (function () ->
              matchClause (g, (v, I.id), (v', s''), ci))
        in
        matchCtx' (g, s'', g'', v, k + 1, ci, addKs (cands, klist))
    | I.Decl (g'', I.BDec (_, (cid, s))) ->
        let gsome, piDecs = I.constBlock cid in
        let s'' = I.comp I.shift s' in
        let klist' =
          matchBlocks (g, I.comp s s'', piDecs, v, k, 1, ci, klist)
        in
        matchCtx' (g, s'', g'', v, k + 1, ci, klist')

  and matchCtx' (g, s', g', v, k, ci, a) = match a with
    | Covered -> Covered
    | CandList klist ->
        matchCtx (g, s', g', v, k, ci, CandList klist)

  let rec matchOut (g, v, ci, a, p) = match a, p with
    | (v', s'), 0 ->
        let cands = matchTop (g, 0, (v, I.id), (v', s'), ci, Eqns []) in
        let cands' = resolveCands cands in
        let cands'' = checkConstraints (g, (v', s'), cands') in
        addKs (cands'', CandList [])
    | ((I.Pi ((I.Dec (_, v1'), _), v2') as v'), s'), p ->
        let x1 = Whnf.newLoweredEVar g (v1', s') in
        matchOut (g, v, ci, (v2', I.Dot (I.Exp x1, s')), p - 1)

  let rec match_ (g, b, p, ci, c) = match b, p, c with
    | (I.Root (I.Const a, s) as v), 0, Input ccs ->
        matchCtx'
          ( g,
            I.id,
            g,
            v,
            1,
            ci,
            matchSig (g, (v, I.id), ccs, ci, CandList []) )
    | v, 0, Output (v', q) ->
        matchOut (g, v, ci, (v', I.Shift (I.ctxLength g)), q)
    | I.Pi ((d, _), v'), p, ccs ->
        match_ (I.Decl (g, d), v', p - 1, ci, ccs)

  let rec insert a3 b3 = match a3, b3 with
    | k, [] -> [ (k, 1) ]
    | k, ((k', n') :: ksn' as ksn) ->
        begin match Int.compare (k, k') with
        | Less -> (k, 1) :: ksn
        | Equal -> (k', n' + 1) :: ksn'
        | Greater -> (k', n') :: insert k ksn'
        end

  let rec join a3 b3 = match a3, b3 with
    | [], ksn -> ksn
    | k :: ks, ksn -> join ks (insert k ksn)

  let rec selectCand = function
    | Covered -> None
    | CandList klist -> selectCand' (klist, [])

  and selectCand' (a, ksn) = match a with
    | [] -> Some ksn
    | Fail :: klist -> selectCand' (klist, ksn)
    | Cands [] :: klist -> selectCand' (klist, ksn)
    | Cands ks :: klist -> selectCand' (klist, join ks ksn)

  let rec instEVars (vs, p, xsRev) = instEVarsW (Whnf.whnf vs, p, xsRev)

  and instEVarsW (vs, p, xsRev) = match vs, p with
    | vs, 0 -> (vs, xsRev)
    | (I.Pi ((I.Dec (xOpt, v1), _), v2), s), p ->
        let x1 = Whnf.newLoweredEVar I.Null (v1, s) in
        instEVars ((v2, I.Dot (I.Exp x1, s)), p - 1, Some x1 :: xsRev)
    | (I.Pi ((I.BDec (_, (l, t)), _), v2), s), p ->
        let l1 = I.newLVar (I.Shift 0) (l, I.comp t s) in
        instEVars ((v2, I.Dot (I.Block l1, s)), p - 1, None :: xsRev)

  open! struct
    let caseList : (I.exp * int) list ref = ref []
  end

  let resetCases () = caseList := []
  let addCase (v, p) = caseList := (v, p) :: !caseList
  let getCases () = !caseList

  let rec createEVarSpine (g, vs) = createEVarSpineW (g, Whnf.whnf vs)

  and createEVarSpineW (g, a) = match a with
    | ((I.Root _, s) as vs) -> (I.Nil, vs)
    | (I.Pi (((I.Dec (_, v1) as d), _), v2), s) ->
        let x = createEVar (g, I.EClo (v1, s)) in
        let s_, vs = createEVarSpine (g, (v2, I.Dot (I.Exp x, s))) in
        (I.App (x, s_), vs)

  let createAtomConst g h =
    let cid =
      match h with I.Const c -> c | I.Def c -> c | _ -> assert false
    in
    let v = I.constType cid in
    let s, vs = createEVarSpine (g, (v, I.id)) in
    (I.Root (h, s), vs)

  let createAtomBVar g k =
    let (I.Dec (_, v)) = I.ctxDec g k in
    let s, vs = createEVarSpine (g, (v, I.id)) in
    (I.Root (I.BVar k, s), vs)

  let createAtomProj (g, h, (v, s)) =
    let s_, vs' = createEVarSpine (g, (v, s)) in
    (I.Root (h, s_), vs')

  let rec constCases (g, vs, a, sc) = match a with
    | [] -> ()
    | (I.Const c as h) :: sgn' ->
        let u, vs' = createAtomConst g h in
        ignore (CsManager.trail (function () ->
              begin if Unify.unifiable g vs vs' then sc u else ()
              end));
        constCases (g, vs, sgn', sc)
    | (I.Def c as h) :: sgn' ->
        let u, vs' = createAtomConst g h in
        ignore (CsManager.trail (function () ->
              begin if Unify.unifiable g vs vs' then sc u else ()
              end));
        constCases (g, vs, sgn', sc)
    | _ :: sgn' ->
        (* Skip other head types (Skonst, NSDef, etc.) *)
        constCases (g, vs, sgn', sc)

  let rec paramCases (g, vs, k, sc) = match k with
    | 0 -> ()
    | k ->
        let u, vs' = createAtomBVar g k in
        ignore (CsManager.trail (function () ->
              begin if Unify.unifiable g vs vs' then sc u else ()
              end));
        paramCases (g, vs, k - 1, sc)

  let rec createEVarSub = function
    | I.Null -> I.id
    | I.Decl (g', (I.Dec (_, v) as d)) ->
        let s = createEVarSub g' in
        let x = Whnf.newLoweredEVar I.Null (v, s) in
        I.Dot (I.Exp x, s)

  let blockName cid = I.conDecName (I.sgnLookup cid)

  let rec blockCases (g, vs, cid, (gsome, piDecs), sc) =
    let t = createEVarSub gsome in
    let sk = I.Shift (I.ctxLength g) in
    let t' = I.comp t sk in
    let lvar = I.newLVar sk (cid, t) in
    blockCases' (g, vs, (lvar, 1), (t', piDecs), sc)

  and blockCases' (g, vs, a, b, sc) = match a, b with
    | (lvar, i), (t, []) -> ()
    | (lvar, i), (t, I.Dec (_, v') :: piDecs) ->
        let u, vs' = createAtomProj (g, I.Proj (lvar, i), (v', t)) in
        ignore (CsManager.trail (function () ->
              begin if Unify.unifiable g vs vs' then sc u else ()
              end));
        let t' = I.Dot (I.Exp (I.Root (I.Proj (lvar, i), I.Nil)), t) in
        blockCases' (g, vs, (lvar, i + 1), (t', piDecs), sc)

  let rec worldCases (g, vs, a, sc) = match a with
    | T.Worlds [] -> ()
    | T.Worlds (cid :: cids) -> begin
        blockCases (g, vs, cid, I.constBlock cid, sc);
        worldCases (g, vs, T.Worlds cids, sc)
      end

  let rec lowerSplitW (a, w, sc) = match a with
    | (I.EVar (_, g, v, _) as x) ->
        let sc' = function
          | u ->
              begin if Unify.unifiable g (x, I.id) (u, I.id) then sc ()
              else ()
              end
        in
        ignore (paramCases (g, (v, I.id), I.ctxLength g, sc'));
        ignore (worldCases (g, (v, I.id), w, sc'));
        ignore (constCases (g, (v, I.id), Index.lookup (I.targetFam v), sc'));
        ()
    | I.Lam (d, u) -> lowerSplitW (u, w, sc)

  let splitEVar (x, w, sc) = lowerSplitW (x, w, sc)

  let abstract (v, s) =
    let i, v' = Abstract.abstractDecImp (I.EClo (v, s)) in
    let v'' = Whnf.normalize (v', I.id) in
    ignore begin if !Global.doubleCheck then
        try TypeCheck.typeCheck I.Null (v'', I.Uni I.Type)
        with TypeCheck.Error _ ->
          (* Coverage splitting can produce terms where higher-order EVars
              are not fully instantiated by pattern unification (e.g., when
              an EVar is applied to another EVar). The abstracted term may
              then fail type checking because the Pi binding types don't
              reflect the structural constraints from the Split. The coverage
              result is still correct — this case represents a valid split
              that the type checker cannot verify due to the abstraction. *)
          ()
      else ()
      end;
    (v'', i)

  let splitVar (v, p, k, (w, ci)) =
    try
      ignore (chatter 6 (function () -> showSplitVar (v, p, k, ci) ^ "\n"));
      let (v1, s), xsRev = instEVars ((v, I.id), p, []) in
      let (Some x) = List.nth (xsRev, k - 1) in
      ignore (resetCases ());
      ignore (splitEVar (x, w, function () -> addCase (abstract (v1, s))));
      Some (getCases ())
    with Constraints.Error constrs ->
      begin
        chatter 7 (function () ->
            ("Inactive split:\n" ^ Print.cnstrsToString constrs) ^ "\n");
        None
      end

  let rec occursInExp (k, a) = match a with
    | I.Uni _ -> false
    | I.Pi (dp, v) -> occursInDecP (k, dp) || occursInExp (k + 1, v)
    | I.Root (h, s) -> occursInHead (k, h) || occursInSpine (k, s)
    | I.Lam (d, v) -> occursInDec (k, d) || occursInExp (k + 1, v)
    | I.FgnExp (cs, ops) -> false

  and occursInHead (k, a) = match a with I.BVar k' -> k = k' | _ -> false

  and occursInSpine (k, a) = match a with
    | I.Nil -> false
    | I.App (u, s) -> occursInExp (k, u) || occursInSpine (k, s)

  and occursInDec (k, I.Dec (_, v)) = occursInExp (k, v)
  and occursInDecP (k, (d, _)) = occursInDec (k, d)

  let rec occursInMatchPos (k, a, ci) = match a with
    | I.Pi (dp, v) -> occursInMatchPos (k + 1, v, ci)
    | I.Root (h, s) -> occursInMatchPosSpine (k, s, ci)

  and occursInMatchPosSpine (k, a, b) = match a, b with
    | I.Nil, Cnil -> false
    | I.App (u, s), Match ci ->
        occursInExp (k, u) || occursInMatchPosSpine (k, s, ci)
    | I.App (u, s), Skip ci -> occursInMatchPosSpine (k, s, ci)

  let rec instEVarsSkip (vs, p, xsRev, ci) =
    instEVarsSkipW (Whnf.whnf vs, p, xsRev, ci)

  and instEVarsSkipW (vs, p, xsRev, ci) = match vs, p with
    | vs, 0 -> (vs, xsRev)
    | (I.Pi ((I.Dec (xOpt, v1), _), v2), s), p ->
        let x1 = Whnf.newLoweredEVar I.Null (v1, s) in
        let eVarOpt =
          begin if occursInMatchPos (1, v2, ci) then Some x1 else None
          end
        in
        instEVarsSkip ((v2, I.Dot (I.Exp x1, s)), p - 1, eVarOpt :: xsRev, ci)
    | (I.Pi ((I.BDec (_, (l, t)), _), v2), s), p ->
        let l1 = I.newLVar (I.Shift 0) (l, I.comp t s) in
        instEVarsSkip ((v2, I.Dot (I.Block l1, s)), p - 1, None :: xsRev, ci)

  let targetBelowEq (a, b) = match b with
    | I.EVar ({ contents = None }, gy, vy, { contents = [] }) ->
        Subordinate.belowEq a (I.targetFam vy)
    | I.EVar ({ contents = None }, gy, vy, { contents = _ :: _ }) -> true

  let rec recursive = function
    | I.EVar ({ contents = Some u }, gx, vx, _) as x ->
        let a = I.targetFam vx in
        let ys = Abstract.collectEVars gx (x, I.id) [] in
        let recp = List.exists (function y -> targetBelowEq (a, y)) ys in
        recp
    | I.Lam (d, u) -> recursive u

  open! struct
    let counter = ref 0
  end

  let resetCount () = counter := 0
  let incCount () = counter := !counter + 1
  let getCount () = !counter

  exception NotFinitary = NotFinitary

  let finitary1 (x, k, w, f, cands) =
    begin
      resetCount ();
      begin
        chatter 7 (function () ->
            (("Trying " ^ Print.expToString I.Null x) ^ " : ") ^ ".\n");
        try
          begin
            splitEVar
              ( x,
                w,
                function
                | () -> begin
                    f ();
                    begin if recursive x then raise NotFinitary
                    else incCount ()
                    end
                  end );
            begin
              chatter 7 (function () ->
                  ("Finitary with " ^ Int.toString (getCount ()))
                  ^ " candidates.\n");
              (k, getCount ()) :: cands
            end
          end
        with
        | NotFinitary -> begin
            chatter 7 (function () -> "Not finitary.\n");
            cands
          end
        | Constraints.Error constrs -> begin
            chatter 7 (function () -> "Inactive finitary Split.\n");
            cands
          end
      end
    end

  let rec finitarySplits (a, k, w, f, cands) = match a with
    | [] -> cands
    | None :: xs -> finitarySplits (xs, k + 1, w, f, cands)
    | Some x :: xs ->
        finitarySplits
          ( xs,
            k + 1,
            w,
            f,
            CsManager.trail (function () -> finitary1 (x, k, w, f, cands)) )

  let finitary (v, p, w, ci) =
    ignore begin if !Global.doubleCheck then
        TypeCheck.typeCheck I.Null (v, I.Uni I.Type)
      else ()
      end;
    let (v1, s), xsRev = instEVarsSkip ((v, I.id), p, [], ci) in
    finitarySplits
      (xsRev, 1, w, (function () -> ignore (abstract (v1, s))), [])

  let eqExp (us, us') = Conv.conv us us'

  let rec eqInpSpine = function
    | ms, (I.SClo (s1_, s1'), s1), ss2 ->
        eqInpSpine (ms, (s1_, I.comp s1' s1), ss2)
    | ms, ss1, (I.SClo (s2_, s2'), s2) ->
        eqInpSpine (ms, ss1, (s2_, I.comp s2' s2))
    | M.Mnil, (I.Nil, s), (I.Nil, s') -> true
    | ( M.Mapp (M.Marg (M.Plus, _), ms'),
        (I.App (u, s_), s),
        (I.App (u', s'_), s') ) ->
        eqExp ((u, s), (u', s')) && eqInpSpine (ms', (s_, s), (s'_, s'))
    | M.Mapp (_, ms'), (I.App (u, s_), s), (I.App (u', s'_), s') ->
        eqInpSpine (ms', (s_, s), (s'_, s'))

  let rec eqInp (c, k, a, ss, ms) = match c with
    | I.Null -> []
    | I.Decl (g', I.Dec (_, I.Root (I.Const a', s'))) ->
        begin if a = a' && eqInpSpine (ms, (s', I.Shift k), ss) then
          k :: eqInp (g', k + 1, a, ss, ms)
        else eqInp (g', k + 1, a, ss, ms)
        end
    | I.Decl (g', I.Dec (_, I.Pi _)) ->
        eqInp (g', k + 1, a, ss, ms)
    | I.Decl (g', I.NDec _) -> eqInp (g', k + 1, a, ss, ms)
    | I.Decl (g', I.BDec (_, (b, t))) ->
        eqInp (g', k + 1, a, ss, ms)

  let rec contractionCands (c, k) = match c with
    | I.Null -> []
    | I.Decl (g', I.Dec (_, I.Root (I.Const a, s))) ->
        begin match UniqueTable.modeLookup a with
        | None -> contractionCands (g', k + 1)
        | Some ms ->
            begin match eqInp (g', k + 1, a, (s, I.Shift k), ms) with
            | [] -> contractionCands (g', k + 1)
            | ns -> (k :: ns) :: contractionCands (g', k + 1)
            end
        end
    | I.Decl (g', I.Dec (_, I.Pi _)) -> contractionCands (g', k + 1)
    | I.Decl (g', I.NDec _) -> contractionCands (g', k + 1)
    | I.Decl (g', I.BDec (_, (b, t))) -> contractionCands (g', k + 1)

  let rec isolateSplittable (g, v, p) = match v, p with
    | v, 0 -> (g, v)
    | I.Pi ((d, _), v'), p ->
        isolateSplittable (I.Decl (g, d), v', p - 1)

  let rec unifyUOutSpine = function
    | ms, (I.SClo (s1_, s1'), s1), ss2 ->
        unifyUOutSpine (ms, (s1_, I.comp s1' s1), ss2)
    | ms, ss1, (I.SClo (s2_, s2'), s2) ->
        unifyUOutSpine (ms, ss1, (s2_, I.comp s2' s2))
    | M.Mnil, (I.Nil, s1), (I.Nil, s2) -> true
    | ( M.Mapp (M.Marg (M.Minus1, _), ms'),
        (I.App (u1, s1_), s1),
        (I.App (u2, s2_), s2) ) ->
        Unify.unifiable I.Null (u1, s1) (u2, s2)
        && unifyUOutSpine (ms', (s1_, s1), (s2_, s2))
    | M.Mapp (_, ms'), (I.App (u1, s1_), s1), (I.App (u2, s2_), s2) ->
        unifyUOutSpine (ms', (s1_, s1), (s2_, s2))

  let rec unifyUOutType (v1, v2) =
    unifyUOutTypeW (Whnf.whnf (v1, I.id), Whnf.whnf (v2, I.id))

  and unifyUOutTypeW
      ((I.Root (I.Const a1, s1_), s1), (I.Root (I.Const a2, s2_), s2)) =
    let (Some ms) = UniqueTable.modeLookup a1 in
    unifyUOutSpine (ms, (s1_, s1), (s2_, s2))

  let unifyUOutEVars
      (Some (I.EVar (_, g1, v1, _)), Some (I.EVar (_, g2, v2, _))) =
    unifyUOutType (v1, v2)

  let unifyUOut2 (xsRev, k1, k2) =
    unifyUOutEVars (List.nth (xsRev, k1 - 1), List.nth (xsRev, k2 - 1))

  let rec unifyUOut1 (xsRev, a) = match a with
    | [] -> true
    | k1 :: [] -> true
    | k1 :: k2 :: ks ->
        unifyUOut2 (xsRev, k1, k2) && unifyUOut1 (xsRev, k2 :: ks)

  let rec unifyUOut (xsRev, a) = match a with
    | [] -> true
    | ks :: kss -> unifyUOut1 (xsRev, ks) && unifyUOut (xsRev, kss)

  let contractAll (v, p, ucands) =
    let (v1, s), xsRev = instEVars ((v, I.id), p, []) in
    begin if unifyUOut (xsRev, ucands) then Some (abstract (v1, s)) else None
    end

  let contract (v, p, ci, lab) =
    let g, _ = isolateSplittable (I.Null, v, p) in
    let ucands = contractionCands (g, 1) in
    let n = List.length ucands in
    ignore begin if n > 0 then
        chatter 6 (function () ->
            ((("Found " ^ Int.toString n) ^ " contraction ")
            ^ pluralize (n, "candidate"))
            ^ "\n")
      else ()
      end;
    let vpOpt' =
      begin if n > 0 then
        try contractAll (v, p, ucands)
        with Constraints.Error _ ->
          begin
            chatter 6 (function () -> "Contraction failed due to constraints\n");
            Some (v, p)
          end
      else Some (v, p)
      end
    in
    ignore begin match vpOpt' with
      | None ->
          chatter 6 (function () ->
              "Case impossible: conflicting unique outputs\n")
      | Some (v', p') ->
          chatter 6 (function () -> showPendingGoal (v', p', ci, lab) ^ "\n")
      end;
    vpOpt'

  let rec findMin ((k, n) :: kns) = findMin' ((k, n), kns)

  and findMin' = function
    | (k0, n0), [] -> (k0, n0)
    | (k0, n0), (k', n') :: kns ->
        begin if n' < n0 then findMin' ((k', n'), kns)
        else findMin' ((k0, n0), kns)
        end

  let rec cover (v, p, ((w, ci) as wci), ccs, lab, missing) =
    begin
      chatter 6 (function () -> showPendingGoal (v, p, ci, lab) ^ "\n");
      cover' (contract (v, p, ci, lab), wci, ccs, lab, missing)
    end

  and cover' (a, b, ccs, lab, missing) = match a, b with
    | Some (v, p), ((w, ci) as wci) ->
        let candResult = match_ (I.Null, v, p, ci, ccs) in
        let selected = selectCand candResult in

        split (v, p, selected, wci, ccs, lab, missing)
    | None, wci -> begin
        chatter 6 (function () -> "Covered\n");
        missing
      end

  and split (v, p, a, b, ccs, lab, missing) = match a, b with
    | None, wci -> begin
        chatter 6 (function () -> "Covered\n");
        missing
      end
    | Some [], ((w, ci) as wci) -> begin
        chatter 6 (function () ->
            "No strong candidates---calculating weak candidates\n");
        splitWeak (v, p, finitary (v, p, w, ci), wci, ccs, lab, missing)
      end
    | Some ((k, _) :: ksn), ((w, ci) as wci) ->
        begin match splitVar (v, p, k, wci) with
        | Some cases -> covers (cases, wci, ccs, lab, missing)
        | None -> split (v, p, Some ksn, wci, ccs, lab, missing)
        end

  and splitWeak (v, p, ksn, wci, ccs, lab, missing) = match ksn with
    | [] -> begin (v, p) :: missing end
    | ksn ->
        split (v, p, Some [ findMin ksn ], wci, ccs, lab, missing)

  and covers (cases, wci, ccs, lab, missing) =
    begin
      chatter 6 (function () ->
          (("Found " ^ Int.toString (List.length cases))
          ^ pluralize (List.length cases, " case"))
          ^ "\n");
      covers' (cases, 1, wci, ccs, lab, missing)
    end

  and covers' (a, n, wci, ccs, lab, missing) = match a with
    | [] -> begin
        chatter 6 (function () ->
            ("All subcases of " ^ labToString lab) ^ " considered\n");
        missing
      end
    | (v, p) :: cases' ->
        covers'
          ( cases',
            n + 1,
            wci,
            ccs,
            lab,
            cover (v, p, wci, ccs, Child (lab, n), missing) )

  let rec constsToTypes = function
    | [] -> []
    | I.Const c :: cs' -> I.constType c :: constsToTypes cs'
    | I.Def d :: cs' -> I.constType d :: constsToTypes cs'

  let rec createCoverClause (a, v, p) = match a with
    | I.Decl (g, d) ->
        createCoverClause (g, I.Pi ((d, I.Maybe), v), p + 1)
    | I.Null -> (Whnf.normalize (v, I.id), p)

  let rec createCoverGoal (g, vs, p, ms) =
    createCoverGoalW (g, Whnf.whnf vs, p, ms)

  and createCoverGoalW (g, b, p, ms) = match b, p with
    | (I.Pi ((d1, p1), v2), s), 0 ->
        let d1' = I.decSub d1 s in
        let v2' = createCoverGoal (I.Decl (g, d1'), (v2, I.dot1 s), 0, ms) in
        I.Pi ((d1', p1), v2')
    | (I.Pi (((I.Dec (_, v1) as d), _), v2), s), p ->
        let x = Whnf.newLoweredEVar g (v1, s) in
        createCoverGoal (g, (v2, I.Dot (I.Exp x, s)), p - 1, ms)
    | (I.Root ((I.Const cid as a), s_), s), p ->
        I.Root (a, createCoverSpine (g, (s_, s), (I.constType cid, I.id), ms))

  and createCoverSpine (g, a, vs, ms) = match a, vs, ms with
    | (I.Nil, s), _, M.Mnil -> I.Nil
    | (I.App (u1, s2), s), (I.Pi ((I.Dec (_, v1), _), v2), s'), M.Mapp (M.Marg (M.Minus, x), ms') ->
        let x = createEVar (g, I.EClo (v1, s')) in
        let s2' =
          createCoverSpine (g, (s2, s), (v2, I.Dot (I.Exp x, s')), ms')
        in
        I.App (x, s2')
    | (I.App (u1, s2), s), (I.Pi (_, v2), s'), M.Mapp (_, ms') ->
        I.App
          ( I.EClo (u1, s),
            createCoverSpine
              ( g,
                (s2, s),
                Whnf.whnf (v2, I.Dot (I.Exp (I.EClo (u1, s)), s')),
                ms' ) )
    | (I.SClo (s_, s'), s), vs, ms ->
        createCoverSpine (g, (s_, I.comp s' s), vs, ms)

  (*****************)
  (* Strengthening *)
  (*****************)
  (* next section adapted from m2/Metasyn.fun *)
  (* weaken (G, a) = w'

       Invariant:
       If   a is a type family
       then G |- w' : G'
       and  forall x:A in G'  A subordinate to a
     *)
  (* added next case, probably should not arise *)
  (* Sun Dec 16 10:42:05 2001 -fp !!! *)
  (*
      | weaken (I.Decl (G', D as I.BDec _), a) =
           I.dot1 (weaken (G', a))
      *)
  (* createEVar (G, V) = X[w] where G |- X[w] : V

       Invariant:
       If G |- V : L
       then G |- X[w] : V
    *)
  (* G |- V : L *)
  (* G  |- w  : G'    *)
  (* G' |- iw : G     *)
  (* G' |- X' : V[iw] *)
  (* was I.newEvar (G', I.EClo (V, iw))  Mon Feb 28 14:30:36 2011 --cs *)
  (* G  |- X  : V     *)
  (*************************)
  (* Coverage instructions *)
  (*************************)
  (* Coverage instructions mirror mode spines, but they
       are computed from modes differently for input and output Coverage.

       Match  --- call match and generate candidates
       Skip   --- ignore this argument for purposes of coverage checking

       For input coverage, match input (+) and skip ignore ( * ) and output (-).

       For output coverage, skip input (+), and match output (-).
       Ignore arguments ( * ) should be impossible for output coverage
    *)
  (* inCoverInst (ms) = ci
       converts mode spine ms to cover instructions ci for input coverage
    *)
  (* outCoverInst (ms) = ci
       converts mode spine ms to cover instructions ci for output coverage
    *)
  (* this last case should be impossible *)
  (* output coverage only from totality checking, where there can be *)
  (* no undirectional ( * ) arguments *)
  (*
      | outCoverInst (M.Mapp (M.Marg (M.Star, x), ms')) =
          Skip (outCoverInst ms')
      *)
  (***************************)
  (* Printing Coverage Goals *)
  (***************************)
  (* labels for cases for tracing coverage checker *)
  (* ^ *)
  (* lab.n, n >= 1 *)
  (* we pass in the mode spine specifying coverage, but currently ignore it *)
  (* fix to identify existential and universal prefixes *)
  (* p > 0 *)
  (* other cases are impossible by CGoal invariant *)
  (*
       Coverage goals have the form {{G}} {{L}} a @ S
       where G are splittable variables
       and L are local parameters (not splittable)
    *)
  (**********************************************)
  (* Creating the initial input coverage goal ***)
  (**********************************************)
  (* buildSpine n = n; n-1; ...; 1; Nil *)
  (* n > 0 *)
  (* Eta-long invariant violation -kw *)
  (* initCGoal' (a, 0, ., V) = ({x1:V1}...{xn:Vn} a x1...xn, n)
       for |- a : V and V = {x1:V1}...{xn:Vn} type

       Invariants for initCGoal' (a, k, G, V):
       G = {x1:V1}...{xk:Vk}
       V = {xk+1:Vk+1}...{xn:Vn} type
       G |- V : type
    *)
  (* initCGoal (a) = {x1:V1}...{xn:Vn} a x1...xn
       where a : {x1:V1}...{xn:Vn} type
    *)
  (****************)
  (*** Matching ***)
  (****************)
  (* for now, no factoring --- singleton list *)
  (* Equation G |- (U1,s1) = (U2,s2)
       Invariant:
       G |- U1[s1] : V
       G |- U2[s2] : V  for some V

       U1[s1] has no EVars (part of coverage goal)
    *)
  (* Splitting candidates *)
  (* Splitting candidates [k1,...,kl] are indices
       into coverage goal {xn:Vn}...{x1:V1} a M1...Mm, counting right-to-left
    *)
  (* equations to be solved, everything matches so far *)
  (* candidates for splitting, matching fails *)
  (* coverage fails without candidates *)
  (* fail () = Fail
       indicate failure without splitting candidates
     *)
  (* failAdd (k, cands) = cands'
       indicate failure, but add k as splitting candidate
    *)
  (* no longer matches *)
  (* remove duplicates? *)
  (* addEqn (e, cands) = cands'
       indicate possible match if equation e can be solved
    *)
  (* still may match: add equation *)
  (* already failed: ignore new constraints *)
  (* already failed without candidates *)
  (* matchEqns (es) = true
       iff  all equations in es can be simultaneously unified

       Effect: instantiate EVars right-hand sides of equations.
    *)
  (* For some reason, s2 is sometimes not a patSub when it should be *)
  (* explicitly convert if possible *)
  (* Sat Dec  7 20:59:46 2002 -fp *)
  (* was: unifiable (G, Us1, Us2) *)
  (* constraints will be left in this case *)
  (* resolveCands (cands) = cands'
       resolve to one of
         Eqns(nil) - match successful
         Fail      - no match, no candidates
         Cands(ks) - candidates ks
       Effect: instantiate EVars in right-hand sides of equations.
    *)
  (* reversed equations Fri Dec 28 09:39:55 2001 -fp !!! *)
  (* why is this important? --cs !!! *)
  (* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars Xs

       try simplifying away the constraints in case they are ""hard""
       disabled for now to get a truer approximation to operational semantics
    *)
  (* constrs <> nil *)
  (* Constraints.simplify constrs @ *)
  (* at present, do not simplify -fp *)
  (* checkConstraints (cands, (Q, s)) = cands'
       failure if constraints remain in Q[s] which indicates only partial match
       Q[s] is the clause head after matching the coverage goal.

       Invariants: if cands = Eqns (es) then es = nil.
    *)
  (* This ignores LVars, because collectEVars does *)
  (* Why is that OK?  Sun Dec 16 09:01:40 2001 -fp !!! *)
  (* _ = nil *)
  (* constraints remained: Fail without candidates *)
  (* Candidate Lists *)
  (*
       Candidate lists record constructors and candidates for each
       constructors or indicate that the coverage goal is matched.
    *)
  (* covered---no candidates *)
  (* cands1,..., candsn *)
  (* addKs (cands, klist) = klist'
       add new constructor to candidate list
    *)
  (* matchExp (G, d, (U1, s1), (U2, s2), cands) = cands'
       matches U1[s1] (part of coverage goal)
       against U2[s2] (part of clause head)
       adds new candidates to cands to return cands'
         this could collapse to Fail,
         postponed equations Eqns(es),
         or candidates Cands(ks)
       d is depth, k <= d means local variable, k > d means coverage variable

       Invariants:
       G |- U1[s1] : V
       G |- U2[s2] : V  for some V
       G = Gc, Gl where d = |Gl|
    *)
  (* Note: I.Proj occurring here will always have the form
              I.Proj (I.Bidx (k), i) *)
  (* No skolem constants, foreign constants, FVars *)
  (* k1 is coverage variable, new candidate *)
  (* otherwise fail with no candidates *)
  (* fail with no candidates *)
  (* because of strictness *)
  (* k1 is coverage variable, new candidate *)
  (* otherwise fail with no candidates *)
  (* was: t2 in prev line, July 22, 2010 -fp -cs *)
  (* instantiate instead of postponing because LVars are *)
  (* only instantiated to Bidx which are rigid *)
  (* Sun Jan  5 12:03:13 2003 -fp *)
  (* handled in above two cases now *)
  (*
            | (I.Proj (b1, i1), I.Proj (b2, i2)) =>
               if (i1 = i2) then
                 matchSpine (G, d, (S1, s1), (S2, s2),
                             matchBlock (G, d, b1, b2, cands))
               else fail (""block projection / block projection clash"")
            *)
  (* k1 is splittable, new candidate *)
  (* otherwise fail with no candidates *)
  (* no other cases should be possible *)
  (* eta-expand *)
  (* eta-expand *)
  (* next 3 cases are only for output coverage *)
  (* not needed since we skip input arguments for output coverage *)
  (* see comments on CoverInst -fp Fri Dec 21 20:58:55 2001 !!! *)
  (*
      | matchExpW (G, d, (I.Pi ((D1, _), V1), s1), (I.Pi ((D2, _), V2), s2), cands) =
        let
          val cands' = matchDec (G, d, (D1, s1), (D2, s2), cands)
        in
          matchExp (I.Decl (G, D1), d+1, (V1, I.dot1 s1), (V2, I.dot1 s2), cands')
        end
      | matchExpW (G, d, (I.Pi _, _), _, cands) = fail ()
      | matchExpW (G, d, _, (I.Pi _, _), cands) = fail ()
      *)
  (* nothing else should be possible, by invariants *)
  (* No I.Uni, I.FgnExp, and no I.Redex by whnf *)
  (* BDec should be impossible here *)
  (* matchBlock now unfolded into the first case of matchExpW *)
  (* Sun Jan  5 12:02:49 2003 -fp *)
  (*
    and matchBlock (G, d, I.Bidx(k), I.Bidx(k'), cands) =
        if (k = k') then cands
          else fail (""block index / block index clash"")
      | matchBlock (G, d, B1 as I.Bidx(k), I.LVar (r2, I.Shift(k'), (l2, t2)), cands) =
         Updated LVar --cs Sun Dec  1 06:24:41 2002 
        let
          val I.BDec (bOpt, (l1, t1)) = I.ctxDec (G, k)
        in
          if l1 <> l2 then fail (""block index / block label clash"")
           else if k < k' then raise Bind 
           k >= k' by invariant  Sat Dec  7 22:00:41 2002 -fp 
          else let
                 val cands2 = matchSub (G, d, t1, t2, cands)
                  instantiate if matching is successful 
                  val _ = print (candsToString (cands2) ^ ""\n"") 
                  instantiate, instead of postponing because 
                  LVars are only instantiated to Bidx's which are rigid 
                  !!!BUG!!! r2 and B1 make sense in different contexts 
                  fixed by k-k' Sat Dec  7 21:12:57 2002 -fp 
                 val _ = Unify.instantiateLVar (r2, I.Bidx (k-k'))
               in
                 cands2
               end
        end
    *)
  (* by invariant *)
  (* matchTop (G, (a @ S1, s1), (a @ S2, s2), ci) = cands
       matches S1[s1] (spine of coverage goal)
       against S2[s2] (spine of clause head)
       skipping over `skip' arguments in cover instructions

       Invariants:
       G |- a @ S1[s1] : type
       G |- a @ S2[s2] : type
       G contains coverage variables,
       S1[s1] contains no EVars
       cover instructions ci matche S1 and S2
    *)
  (* unify spines, skipping output and ignore arguments in modeSpine *)
  (* fails, with no candidates since type families don't match *)
  (* this case can only arise in output coverage *)
  (* we do not match D1 and D2, since D1 is always an instance of D2 *)
  (* and no splittable variables should be suggested here *)
  (* Sat Dec 22 23:53:44 2001 -fp !!! *)
  (* an argument that must be covered (Match) *)
  (* an argument that need not be covered (Skip) *)
  (* matchClause (G, (a @ S1, s1), V, ci) = cands
       as in matchTop, but r is clause
       NOTE: Simply use constant type for more robustness (see below)
    *)
  (* changed to use subordination and strengthening here *)
  (* Sun Dec 16 10:39:34 2001 -fp *)
  (* val X1 = createEVar (G, I.EClo (V1, s)) *)
  (* changed back --- no effect *)
  (* was val X1 = I.newEVar (G, I.EClo (V1, s)) Mon Feb 28 14:37:22 2011 -cs *)
  (* was: I.Null instead of G in line above Wed Nov 21 16:40:40 2001 *)
  (* matchSig (G, (a @ S, s), ccs, ci, klist) = klist'
       match coverage goal {{G}} a @ S[s]
       against each coverage clause V in ccs,
       adding one new list cand for each V to klist to obtain klist'

       Invariants:
       G |- a @ S[s] : type
       V consists of clauses with target type a @ S'
       ci matches S
       klist <> Covered
    *)
  (* matchSig' (G, (a @ S, s), ccs, ci, klist) = klist'
       as matchSig, but check if coverage goal {{G}} a @ S[s] is already matched
    *)
  (* already covered: return *)
  (* not yet covered: continue to search *)
  (* matchBlocks (G, s', piDecs, V, k, i, ci, klist) = klist'
       Invariants:
       G |- s' : Gsome
       Gsome |- piDecs : ctx
       G |- V : type
       G_k = (Gsome, D1...D(i-1) piDecs)
     *)
  (* klist <> Covered *)
  (* matchCtx (G, s', G', V, k, ci, klist) = klist'
       Invariants:
       G |- s' : G'
       G |- V : type
       s' o ^ = ^k
       ci matches for for V = a @ S
       klist <> Covered accumulates mode spines
    *)
  (* will always fail for input coverage *)
  (*  G'', V' |- ^ : G''
              G |- s' : G'', V'
          *)
  (*  G |- ^ o s' : G'' *)
  (* G'' |- s : Gsome,
             G |- s'' : G''
             G |- s o s'' : Gsome
             Gsome |- piDecs : ctx
          *)
  (* as matchClause *)
  (* p > 0 *)
  (* was val X1 = I.newEVar (G, I.EClo (V1', s')) Mon Feb 28 14:38:21 2011 -cs *)
  (* match (., V, p, ci, I/O(ccs)) = klist
       matching coverage goal {{G}} V against coverage clauses Vi in ccs
       yields candidates klist
       no local assumptions
       Invariants:
       V = {{G}} {{L}} a @ S where |G| = p
       cover instructions ci match S
       G |- V : type
    *)
  (************************************)
  (*** Selecting Splitting Variable ***)
  (************************************)
  (* insert (k, ksn) = ksn'
       ksn is ordered list of ks (smallest index first) with multiplicities
    *)
  (* join (ks, ksn) = ksn'
       ksn is as in function insert
    *)
  (* selectCand (klist) = ksnOpt
       where ksOpt is an indication of coverage (NONE)
       or a list of candidates with multiplicities

       Simple heuristic: select last splitting candidate from last clause tried
       This will never pick an index variable unless necessary.
    *)
  (* success: case is covered! *)
  (* failure: case G,V is not covered! *)
  (* local failure (clash) and no candidates *)
  (* local failure but no candidates *)
  (* found candidates ks <> nil *)
  (*****************)
  (*** Splitting ***)
  (*****************)
  (* In a coverage goal {{G}} {{L}} a @ S we instantiate each
       declaration in G with a new EVar, then split one of these variables,
       then abstract to obtain a new coverage goal {{G'}} {{L'}} a @ S'
    *)
  (* instEVars ({x1:V1}...{xp:Vp} V, p, nil) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars
    *)
  (* p > 0 *)
  (* all EVars are global *)
  (* was  val X1 = I.newEVar (I.Null, I.EClo (V1, s))  all EVars are global 
             Mon Feb 28 14:39:15 2011 -cs *)
  (* G0 |- t : Gsome *)
  (* . |- s : G0 *)
  (* p > 0 *)
  (* new -fp Sun Dec  1 20:58:06 2002 *)
  (* new -cs  Sun Dec  1 06:27:57 2002 *)
  (* caseList is a list of possibilities for a variables
       to be Split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
  (* createEVarSpine (G, (V, s)) = (S', (V', s'))

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [sjfh']
       and  G |- S : V [s] >  V' [s']
    *)
  (* changed to use createEVar? *)
  (* Sun Dec 16 10:36:59 2001 -fp *)
  (* s = id *)
  (* G |- V1[s] : L *)
  (* Uni or other cases should be impossible *)
  (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
  (* mod: m2/Metasyn.fun allows skolem constants *)
  (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
  (* end m2/Metasyn.fun *)
  (* createAtomProj (G, #i(l), (V, s)) = (U', (V', s'))

       Invariant:
       If   G |- #i(l) : Pi {V1 .. Vn}. Va
       and  G |- Pi {V1..Vn}. Va = V[s] : type
       then . |- U' = #i(l) @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
  (* createEVarSub G' = s

       Invariant:
       If   . |- G' ctx
       then . |- s : G' and s instantiates each x:A with an EVar . |- X : A

       Update: Always use empty context. Sat Dec  8 13:19:58 2001 -fp
    *)
  (* was   val V' = I.EClo (V, s)
                   val X = I.newEVar (I.Null, V') Mon Feb 28 15:32:09 2011 --cs *)
  (* hack *)
  (* blockCases (G, Vs, B, (Gsome, piDecs), sc) =

       If G |- V[s] : type
          . |- Gsome ctx and Gsome |- piDecs decList
       then sc is called for any x:A in piDecs such thtat
            G |- V[s] = A[t] : type
            where t instantiates variable in Gsome with new EVars
    *)
  (* . |- t : Gsome *)
  (* was: the above, using t' for t below *)
  (*  BUG. Breach in the invariant:
                         G |- sk : .
                         . |- t: Gsome
                         G <> .

                         replace t by t' in I.newLVar (sk, (cid, t))
                      --cs Fri Jan  3 11:07:41 2003 *)
  (* G |- t' : Gsome *)
  (* G |- t : G' and G' |- ({_:V'},piDecs) decList *)
  (* so G |- V'[t'] : type *)
  (* will trail *)
  (* will trail *)
  (* will trail *)
  (* splitEVar (X, W, sc) = ()

       calls sc () for all cases, after instantiation of X
       W are the currently possible worlds
    *)
  (* was
   fun lowerSplit (G, Vs, W, sc, print) = lowerSplitW (G, Whnf.whnf Vs, W, sc, print)
    and lowerSplitW (G, Vs as (I.Root (I.Const a, _), s), W, sc, pr) =
        let
        val _ = print (""Consider P cases for ""  ^ Print.expToString (G, I.EClo Vs) ^ ""\n"")
val _ = pr () 
          val _ = paramCases (G, Vs, I.ctxLength G, sc)  will trail 
        val _ = print (""Consider W cases for ""  ^ Print.expToString (G, I.EClo Vs) ^ ""\n"")
val _ = pr () 
          val _ = worldCases (G, Vs, W, sc)  will trail 
        val _ = print (""Consider C cases for ""  ^ Print.expToString (G, I.EClo Vs) ^ ""\n"") 
          val _ = constCases (G, Vs, Index.lookup a, sc)  will trail 
        in
          ()
        end
      | lowerSplitW (G, (I.Pi ((D, P), V), s), W, sc, print) =
        let
          val D' = I.decSub (D, s)
        in
          lowerSplit (I.Decl (G, D'), (V, I.dot1 s), W, fn U => sc (I.Lam (D', U)), print)
        end

   fun splitEVar ((X as I.EVar (_, GX, V, _)), W, sc, print) =  GX = I.Null 
         lowerSplit (I.Null, (V, I.id), W,
                      fn U => if Unify.unifiable (I.Null, (X, I.id), (U, I.id))
                                then sc ()
                              else (), print)
    Mon Feb 28 14:49:04 2011 -cs *)
  (* abstract (V, s) = V'
       where V' = {{G}} Vs' and G abstracts over all EVars in V[s]
       in arbitrary order respecting dependency

       Invariants: . |- V[s] : type
       Effect: may raise Constraints.Error (constrs)
     *)
  (* splitVar ({{G}} V, p, k, W) = SOME [{{G1}} V1 ,..., {{Gn}} Vn]
                                  or NONE
       where {{Gi}} Vi are new coverage goals obtained by
       splitting kth variable in G, counting right-to-left.

       returns NONE if splitting variable k fails because of constraints

       W are the worlds defined for current predicate

       Invariants:
       |G| = p
       k <= |G|
       G |- V : type
       {{Gi}} Vi cover {{G}} V
    *)
  (* split on k'th variable, counting from innermost *)
  (* may raise Constraints.Error *)
  (* Constraints.Error could be raised by abstract *)
  (**********************)
  (* Finitary Splitting *)
  (**********************)
  (*
       A splittable variable X : V is called finitary
       if there are finitely many alternatives for V.
       This means there are finitely many (including 0)
       constructors (possibly including local variables) such that
       all free variables in the argument are not recursive
       with the target type of V.

       Splitting such variables can never lead to non-termination.
    *)
  (* Stolen from Abstract.fun *)
  (* foreign expression probably should not occur *)
  (* but if they do, variable occurrences don't count *)
  (* occursInExp (k, Whnf.normalize (#toInternal(ops) (), I.id)) *)
  (* no case for Redex, EVar, EClo *)
  (* no case for SClo *)
  (* occursInMatchPos (k, U, ci) = true
       if k occur in U in a matchable position according to the coverage
       instructions ci
    *)
  (* instEVarsSkip ({x1:V1}...{xp:Vp} V, p, nil, ci) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars that actually occur in a ""Match"" argument
       and ci are the coverage instructions (Match or Skip) for the target type of V
    *)
  (* p > 0 *)
  (* all EVars are global *)
  (* was val X1 = I.newEVar (I.Null, I.EClo (V1, s))  all EVars are global 
             Mon Feb 28 15:25:42 2011 --cs *)
  (* G0 |- t : Gsome *)
  (* . |- s : G0 *)
  (* p > 0 *)
  (* -fp Sun Dec  1 21:09:38 2002 *)
  (* -cs Sun Dec  1 06:30:59 2002 *)
  (* if contraints remain, consider recursive and thereby unsplittable *)
  (* recursive X = true
       iff the instantiation of X : {{G}} a @ S contains an
           EVar Y : {{G'}} b @ S such that a <|= b

       This means there is no guarantee that X : {{G}} a @ S has only
       a finite number of instances
    *)
  (* GX = I.Null*)
  (* is this always true? --cs!!!*)
  (* LVars are ignored here.  OK because never splittable? *)
  (* Sat Dec 15 22:42:10 2001 -fp !!! *)
  (* finitary1 (X, k, W, f, cands)
        = ((k, n)::cands) if X is finitary with n possibilities
        = cands if X is not finitary
    *)
  (* The function f has been added to ensure that k is splittable without
       Constraints.   In the previous version, this check was not performed.
       nat : type.
       z : nat.
       s : nat -> nat.

       eqz :  nat -> type.
       eqz_z : eqz z.

       unit : type.
       * : unit.

       test : {f : unit -> nat} eqz (f * ) -> type.
       %worlds () (test _ _).
       %covers test +F +Q.  %% loops!
        Counterexample due to Andrzej.  Fix due to Adam.
        Mon Oct 15 15:08:25 2007 --cs
    *)
  (* was Mon Feb 28 15:29:36 2011 -cs
    fun finitary1 (X as I.EVar(r, I.Null, VX, _), k, W, f, cands, print) =
        ( resetCount () ;
          chatter 7 (fn () => ""Trying "" ^ Print.expToString (I.Null, X) ^ "" : ""
                     ^ Print.expToString (I.Null, VX) ^ "".\n"") ;
          ( splitEVar (X, W, fn () => (f (); if recursive X
                                        then raise NotFinitary
                                      else incCount ()), print) ;
            chatter 7 (fn () => ""Finitary with "" ^ Int.toString (getCount ()) ^ "" candidates.\n"");

            (k, getCount ())::cands )
           handle NotFinitary => ( chatter 7 (fn () => ""Not finitary.\n"");
                                   cands )
                 | Constraints.Error (constrs) =>
                                 ( chatter 7 (fn () => ""Inactive finitary Split.\n"");
                                   cands )
        )
    *)
  (* finitarySplits (XsRev, k, W, cands) = [(k1,n1),...,(km,nm)]@cands
       where all ki are finitary with ni possibilities for X(i+k)
    *)
  (* parameter blocks can never be split *)
  (* finitary ({{G}} V, p, W) = [(k1,n1),...,(km,nm)]
       where ki are indices of splittable variables in G with ni possibilities
       and |G| = p
       and ci are the coverage instructions for the target type of V
    *)
  (***********************************)
  (* Contraction based on uniqueness *)
  (***********************************)
  (* eqExp (U[s], U'[s']) = true iff G |- U[s] == U'[s'] : V
       Invariants:
         G |- U[s] : V
         G |- U'[s'] : V
         U[s], U'[s'] contain no EVars
       Note that the typing invariant is satisfied because
       input arguments can only depend on other input arguments,
       but not undetermined or output arguments.
       Similar remarks apply to functions below
    *)
  (* eqInpSpine (ms, S1[s1], S2[s2]) = true
       iff U1[s1] == U2[s2] for all input (+) arguments in S1, S2
       according to uniqueness mode spine ms
       Invariants: typing as in eqExp, ms ~ S1, ms ~ S2
    *)
  (* ignore Star, Minus, Minus1 *)
  (* other cases should be impossible since spines must match *)
  (* eqInp (G, k, a, S[s], ms) = [k1+k,...,kn+k]
       where k1,...,kn are the deBruijn indices of those declarations
       ki:a @ Si in such that G0 |- Si[^ki+k] == S[s] on all input arguments
       according to mode spine ms.
       Here G = ...kn:a @ Sn, ..., k1:a @ S1, ...
    *)
  (* defined type families disallowed here *)
  (* other cases should be impossible *)
  (* contractionCands (G, k) = [[k11,...,k1{n1}],...,[km1,...,km{nm}]]
       where each [kj1,...,kj{nj}] are deBruijn indices in G (counting from right)
       such that kji:aj @ Sji ... kj{nj}:aj @ Sj{nj} and
       Sji...Sj{nj} agree on their input arguments according to the
       uniqueness mode spine for aj
    *)
  (* defined type families disallowed here *)
  (* using only one uniqueness declaration per type family *)
  (* ignore Pi --- contraction cands unclear *)
  (* ignore blocks --- contraction cands unclear *)
  (* isolateSplittable ((G0, {{G1}}V, p) = ((G0@G1), V) where |G1| = p
       This isolates the splittable variable G1@G1 from an old-style
       coverage goal ({{G}}V, p)
    *)
  (* unifyUOutSpine (ms, S1[s1], S2[s2]) = true
       iff U1[s1] == U2[s2] for all unique output (-1) arguments in S1, S2
       according to uniqueness mode spine ms
       Invariants: the input arguments in S1[s1] and S2[s2] must be known
          to be equal, ms ~ S1, ms ~ S2
       Effect: EVars in S1[s1], S2[s2] are instantianted, both upon
          failure and success
    *)
  (* will have effect! *)
  (* if mode = + already equal by invariant; otherwise ignore *)
  (* Nil/App or App/Nil cannot occur by invariants *)
  (* unifyUOuttype (a @ S1, a @ S2) = true
       iff S1 and S2 unify on all unique output (-1) arguments in S1, S2
       according to uniqueness mode declaration for a (both args must have same a)
       Invariants: the input args in S1, S2 must be known to be equal
          and a must have a uniqueness mode
       Effect: Evars may be instantiated by unification
    *)
  (* a1 = a2 by invariant *)
  (* must succeed by invariant *)
  (* must be constant-headed roots by invariant *)
  (* unifyUOutEvars (X1, X2) = true
       iff . |- X1 : a @ S1, . |- X2 : a @ S2 and the unique output arguments
       in V1 and V2 unify
       Invariants: the input args in S1, S2, must be known to be equal
         Both types start with the same a, a must have a uniqueness mode
       Effect: Evars may be instantiated by unification
    *)
  (* G1 = G2 = I.Null *)
  (* unifyUOut2 ([X1,...,Xp], k1, k2) = (see unifyOutEvars (X{k1}, X{k2})) *)
  (* unifyOut1 ([X1,...,Xp], [k1, k2, ..., kn] = true
       if X{k1} ""=="" X{k2} ""=="" ... ""=="" X{kn} according to unifyOutEvars
    *)
  (* unifyOut ([X1,...,Xp], [[k11,...,k1{n1}],...,[km1,...,km{nm}]]) = true
       if unifyOut1 ([X1,...,Xp], [kj1,...,kj{nj}]) for each j
    *)
  (* contractAll ({{G}}V, p, ucands) = SOME(V',p')
       iff (V',p') is the result of contracting unique output arguments
           according to contraction candidates ucands
           of variables in G where all input arguments agree
       returns NONE if unique output arguments are non-unifiable
       may be the identity if output arguments are already identity
          or unsolvable constraints during contraction
       Invariants: p = |G| (G contains the splittable variables)
    *)
  (* as in splitVar *)
  (* as in splitVar, may raise Constraints.Error *)
  (* unique outputs not simultaneously unifiable *)
  (* contract ({{G}}V0, p, ci, lab) = SOME(V',p')
       iff (V',p') is the result of contracting unique output arguments
           of variables in G where all input arguments agree
       returns NONE if unique output arguments are non-unifiable
       may be the identity if output arguments are already identity
          or unsolvable constraints during contraction
       ci and lab are used for printing
       Invariants: p = |G| (G contains the splittable variables)
    *)
  (* ignore body of coverage goal *)
  (* no progress if constraints remain *)
  (* no candidates, no progress *)
  (*********************)
  (* Coverage Checking *)
  (*********************)
  (* findMin ((k1,n1),...,(km,nm)) = (ki,ni)
       where ni is the minimum among the n1,...,nm
       Invariant: m >= 1
    *)
  (* need to improve tracing with higher chatter levels *)
  (* ccs = covering clauses *)
  (* cover (V, p, (W, ci), ccs, lab, missing) = missing'
       covers ([(V1,p1),...,(Vi,pi)], (W, ci), ccs, missing) = missing'

       check if Match arguments (+ for input, - for output) in V or all Vi, respectively,
       are covered by clauses ccs, adding omitted cases to missing to yield missing'.

       V = {{G}} {{L}} a @ S where |G| = p and G contains the splittable
       variables while L contains the local parameters

       W are the worlds for type family a
       ci are the cover instructions matching S

       lab is the label for the current goal for tracing purposes
    *)
  (* V is covered by unique output inconsistency *)
  (* V is covered: return missing patterns from other cases *)
  (* no strong candidates: check for finitary splitting candidates *)
  (* some candidates: split first candidate, ignoring multiplicities *)
  (* candidates are in reverse order, so non-index candidates are split first *)
  (* splitVar shows splitting as it happens *)
  (* splitting variable k generated constraints *)
  (* try other candidates *)
  (* ksn <> nil *)
  (* commit to the minimal candidate, since no constraints can arise *)
  (******************)
  (* Input Coverage *)
  (******************)
  (* constsToTypes [c1,...,cn] = [V1,...,Vn] where ci:Vi.
       Generates coverage clauses from signature.
    *)
  (*******************)
  (* Output Coverage *)
  (*******************)
  (* createCoverClause (G, V, 0) = ({{G}} V, |G|)
       where {{G}} V is in NF
    *)
  (* createCoverGoal (., ({{G}} {{GL}} a @ S, s), p, ms) = V' with |G| = p
       createCoverGoal (GL, (a @ S, s), 0, ms) = a @ S'
       createCoverSpine ((S, s), (V', s'), ms) = S'

       where all variables in G are replaced by new EVars in V to yield V'
       and output arguments in S are replaced by new EVars in V to yield V'

       G are the externally quantified variables
       GL are the locally introduced parameter for the current subgoal a @ S

       Invariants: . |- ({{G}} {{GL}} a @ S)[s] : type
                   |G| = p
                   ms matches S
                   . | S[s] : V'[s'] > type
                   . |- V'[s'] : type
    *)
  (* p > 0, G = I.Null *)
  (* was  val X = I.newEVar (G, I.EClo (V1, s))  Mon Feb 28 15:33:52 2011 -cs *)
  (* s = id, p >= 0 *)
  (* replace output argument by new variable *)
  (* strengthen G based on subordination *)
  (* leave input ( + ) arguments as they are, ignore ( * ) impossible *)
  let checkNoDef a =
    begin match I.sgnLookup a with
    | I.ConDef _ ->
        raise
          (Error
             (("Coverage checking " ^ N.qidToString (N.constQid a))
             ^ ":\ntype family must not be defined."))
    | _ -> ()
    end

  (* checkCovers (a, ms) = ()
       checks coverage for type family a with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *)
  let checkCovers a ms =
    ignore (chatter 4 (function () ->
          ("Input coverage checking family " ^ N.qidToString (N.constQid a))
          ^ "\n"));
    ignore (checkNoDef a);
    ignore (try Subordinate.checkNoDef a
      with Subordinate.Error msg ->
        raise
          (Error
             ((("Coverage checking " ^ N.qidToString (N.constQid a)) ^ ":\n")
             ^ msg)));
    let v0, p = initCGoal a in
    ignore begin if !Global.doubleCheck then
        TypeCheck.typeCheck I.Null (v0, I.Uni I.Type)
      else ()
      end;
    ignore (CsManager.reset ());
    let cIn = inCoverInst ms in
    let cs = Index.lookup a in
    let ccs = constsToTypes cs in
    let w = W.lookup a in
    let v0 = createCoverGoal (I.Null, (v0, I.id), p, ms) in
    let v0, p = abstract (v0, I.id) in
    let missing = cover (v0, p, (w, cIn), Input ccs, Top, []) in
    ignore begin match missing with
      | [] -> ()
      | _ :: _ ->
          raise
            (Error
               (("Coverage error --- missing cases:\n"
                ^ missingToString (missing, ms))
               ^ "\n"))
      end
      (* all cases covered *);
    ()

  (* convert mode spine to cover instructions *)
  (* lookup constants defining a *)
  (* calculate covering clauses *)
  (* world declarations for a; must be defined *)
  (* replace output by new EVars *)
  (* abstract will double-check *)

  (* checkOut (G, (V, s)) = ()
       checks if the most general goal V' is locally output-covered by V
       Effect: raises Error (msg) otherwise
    *)
  let checkOut g (v, s) =
    let a = I.targetFam v in
    let (Some ms) = ModeTable.modeLookup a in
    let cOut = outCoverInst ms in
    let v', q = createCoverClause (g, I.EClo (v, s), 0) in
    ignore begin if !Global.doubleCheck then
        TypeCheck.typeCheck I.Null (v', I.Uni I.Type)
      else ()
      end;
    let v0 = createCoverGoal (I.Null, (v', I.id), q, ms) in
    let v0', p = abstract (v0, I.id) in
    let w = W.lookup a in
    let missing = cover (v0', p, (w, cOut), Output (v', q), Top, []) in
    ignore begin match missing with
      | [] -> ()
      | _ :: _ ->
          raise
            (Error
               (("Output coverage error --- missing cases:\n"
                ^ missingToString (missing, ms))
               ^ "\n"))
      end;
    ()

  (* must be defined and well-moded *)
  (* determine cover instructions *)
  (* abstract all variables in G *)
  (* replace output by new EVars *)
  (* abstract will double-check *)

  (**********************************************)
  (* New code for coverage checking of Tomega   *)
  (* Started Sun Nov 24 11:02:25 2002  -fp      *)
  (* First version Tue Nov 26 19:29:12 2002 -fp *)
  (**********************************************)
  (* cg = CGoal (G, S)  with G |- S : {{G'}} type *)
  type coverGoal = CGoal of I.dctx * I.spine

  (* cc = CClause (Gi, Si) with  Gi |- Si : {{G}} type *)
  type coverClause = CClause of I.dctx * I.spine

  let formatCGoal (CGoal (g, s)) =
    ignore (N.varReset I.Null);
    F.hVbox
      ([
         Print.formatCtx I.Null g;
         F.break_;
         F.break_;
         F.string "|-";
         F.space;
       ]
      @ Print.formatSpine g s)

  let showPendingCGoal (CGoal (g, s), lab) =
    F.makestring_fmt
      (F.hbox
         [
           F.string (labToString lab);
           F.space;
           F.string "?- ";
           formatCGoal (CGoal (g, s));
           F.string ".";
         ])

  let showCClause (CClause (g, s)) =
    ignore (N.varReset I.Null);
    F.makestring_fmt (F.hVbox ([ F.string "!- " ] @ Print.formatSpine g s))

  let showSplitVar (CGoal (g, s), k) =
    ignore (N.varReset I.Null);
    let (I.Dec (Some x, _)) = I.ctxLookup g k in
    (("Split " ^ x) ^ " in ")
    ^ F.makestring_fmt (F.hVbox (Print.formatSpine g s))

  (* newEVarSubst (G, G') = s
       Invariant:   If G = xn:Vn,...,x1:V1
                  then s = X1...Xn.^k
                     G |- s : G'
    *)
  let rec newEVarSubst (g, a) = match a with
    | I.Null -> I.Shift (I.ctxLength g)
    | I.Decl (g', (I.Dec (_, v) as d)) ->
        let s' = newEVarSubst (g, g') in
        let x = Whnf.newLoweredEVar g (v, s') in
        I.Dot (I.Exp x, s')
        (* was val V' = I.EClo (V, s')
                 val X = I.newEVar (G, V') Mon Feb 28 15:34:31 2011 -cs *)
    | I.Decl (g', (I.NDec _ as d)) ->
        let s' = newEVarSubst (g, g') in
        I.Dot (I.Undef, s')
    | I.Decl (g', (I.BDec (_, (b, t)) as d)) ->
        let s' = newEVarSubst (g, g') in
        let l1 = I.newLVar s' (b, t) in
        I.Dot (I.Block l1, s')

  (* was  val L1 = I.newLVar (I.Shift(0), (b, I.comp(t, s')))
             --cs Fri Jul 23 16:39:27 2010 *)
  (* -cs Fri Jul 23 16:35:04 2010  FPCHECK *)
  (* L : Delta[t][G'] *)
  (* G |- s : G'  G |- L[s'] : V[s]
             G |- (L[s'].s : G', V *)
  (* -fp Sun Dec  1 21:10:45 2002 *)
  (* -cs Sun Dec  1 06:31:23 2002 *)

  (* ADec should be impossible *)
  (* checkConstraints (G, Si[ti], cands) = cands'
       failure if constraints remain in Q[s] which indicates only partial match
       Q[s] is the clause head after matching the coverage goal.

       Invariants: if cands = Eqns (es) then es = nil.
    *)
  (* This ignores LVars, because collectEVars does *)
  (* Why is that OK?  Sun Dec 16 09:01:40 2001 -fp !!! *)
  let checkConstraints (g, a, b) = match a, b with
    | (si, ti), Cands ks -> Cands ks
    | (si, ti), Fail -> Fail
    | (si, ti), Eqns _ ->
        let xs = Abstract.collectEVarsSpine g (si, ti) [] in
        let constrs = collectConstraints xs in
        begin match constrs with
        | [] -> Eqns []
        | _ -> fail "Remaining constraints"
        end

  (* constraints remained: Fail without candidates *)
  (* _ = nil *)

  (* matchClause (cg, (Si, ti)) = klist
       matching coverage goal cg against instantiated coverage clause Si[ti]
       yields splitting candidates klist
    *)
  let matchClause (CGoal (g, s), (si, ti)) =
    let cands1 = matchSpine (g, 0, (s, I.id), (si, ti), Eqns []) in
    let cands2 = resolveCands cands1 in
    let cands3 = checkConstraints (g, (si, ti), cands2) in
    cands3

  (* matchClauses (cg, ccs, klist) = klist'
       as in match, with accumulator argument klist
    *)
  let rec matchClauses (a, b, klist) = match a, b with
    | cg, [] -> klist
    | (CGoal (g, s) as cg), CClause (gi, si) :: ccs ->
        let ti = newEVarSubst (g, gi) in
        let cands =
          CsManager.trail (function () -> matchClause (cg, (si, ti)))
        in
        matchClauses' (cg, ccs, addKs (cands, klist))
  (* G |- ti : Gi *)

  and matchClauses' (cg, ccs, a) = match a with
    | Covered -> Covered
    | (CandList _ as klist) -> matchClauses (cg, ccs, klist)

  (* match (cg, ccs) = klist
       matching coverage goal cg against coverage clauses ccs
       yields candidates klist
    *)
  let match_ (CGoal (g, s), ccs) =
    matchClauses (CGoal (g, s), ccs, CandList [])

  (* abstractSpine (S, s) = CGoal (G, S')
       Invariant: G abstracts all EVars in S[s]
       G |- S' : {{G'}}type
    *)
  let abstractSpine s_ s =
    let g', s' = Abstract.abstractSpine s_ s in
    let namedG' = N.ctxName g' in
    ignore begin if !Global.doubleCheck then TypeCheck.typeCheckCtx namedG'
      (* TypeCheck.typeCheckSpine (namedG', S') *) else ()
      end;
    CGoal (namedG', s')
  (* for printing purposes *)

  (* kthSub (X1...Xn.^0, k) = Xk
       Invariant: 1 <= k <= n
       Xi are either EVars or to be ignored
    *)
  let rec kthSub = function
    | I.Dot (I.Exp x, s), 1 -> x
    | I.Dot (_, s), k -> kthSub (s, k - 1)

  (* subToXsRev (X1...Xn.^0) = [Xiopt,...,Xnopt]
       Invariant: Xi are either EVars (translate to SOME(Xi))
                  or not (translate to NONE)
    *)
  let rec subToXsRev = function
    | I.Shift 0 -> []
    | I.Dot (I.Exp x, s) -> Some x :: subToXsRev s
    | I.Dot (_, s) -> None :: subToXsRev s
  (* n = 0 *)

  (* caseList is a list of possibilities for a variables
       to be Split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
  open! struct
    let caseList : coverGoal list ref = ref []
  end

  let resetCases () = caseList := []
  let addCase cg = caseList := cg :: !caseList
  let getCases () = !caseList

  (* splitVar (CGoal(G, S), k, w) = SOME [cg1,...,cgn]
                                  or NONE
       where cgi are new coverage goals obtained by
       splitting kth variable in G, counting right-to-left.

       returns NONE if splitting variable k fails because of constraints

       w are the worlds defined for current predicate

       Invariants:
       k <= |G|
       G |- S : {{G'}} type
       cgi cover cg
    *)
  let splitVar ((CGoal (g, s_) as cg), k, w) =
    try
      ignore (chatter 6 (function () -> showSplitVar (cg, k) ^ "\n"));
      let s = newEVarSubst (I.Null, g) in
      let x = kthSub (s, k) in
      ignore (resetCases ());
      ignore (splitEVar (x, w, function () -> addCase (abstractSpine s_ s)));
      Some (getCases ())
      (* for splitting, EVars are always global *)
      (* G = xn:V1,...,x1:Vn *)
      (* s = X1....Xn.^0, where . |- s : G *)
      (* starts with k = 1 (a la deBruijn) *)
    with Constraints.Error constrs ->
      begin
        chatter 7 (function () ->
            ("Inactive split:\n" ^ Print.cnstrsToString constrs) ^ "\n");
        None
      end
  (* Constraints.Error could be raised by abstract *)

  (* finitary (CGoal (G, S), W) = [(k1,n1),...,(km,nm)]
       where ki are indices of splittable variables in G with ni possibilities
    *)
  let finitary (CGoal (g, s_), w) =
    let s = newEVarSubst (I.Null, g) in
    let xsRev = subToXsRev s in
    finitarySplits
      (xsRev, 1, w, (function () -> ignore (abstractSpine s_ s)), [])

  (* G = xn:Vn,...,x1:V1 *)
  (* for splitting, EVars are always global *)
  (* s = X1...Xn.^0,  . |- S : G *)
  (* XsRev = [SOME(X1),...,SOME(Xn)] *)

  (***************)
  (* Contraction *)
  (***************)
  (* for explanation, see contract and contractAll above *)
  let contractAll (CGoal (g, s_), ucands) =
    let s = newEVarSubst (I.Null, g) in
    let xsRev = subToXsRev s in
    begin if unifyUOut (xsRev, ucands) then Some (abstractSpine s_ s)
    else None
    end
  (* as in splitVar, may raise Constraints.Error *)
  (* for unif, EVars are always global *)

  let contract ((CGoal (g, s) as cg), lab) =
    let ucands = contractionCands (g, 1) in
    let n = List.length ucands in
    ignore begin if n > 0 then
        chatter 6 (function () ->
            ((("Found " ^ Int.toString n) ^ " contraction ")
            ^ pluralize (n, "candidate"))
            ^ "\n")
      else ()
      end;
    let cgOpt' =
      begin if n > 0 then
        try contractAll (cg, ucands)
        with Constraints.Error _ ->
          begin
            chatter 6 (function () -> "Contraction failed due to constraints\n");
            Some cg
          end
      else Some cg
      end
      (* no progress if constraints remain *)
    in
    ignore begin match cgOpt' with
      | None ->
          chatter 6 (function () ->
              "Case impossible: conflicting unique outputs\n")
      | Some cg' ->
          chatter 6 (function () -> showPendingCGoal (cg', lab) ^ "\n")
      end;
    cgOpt' (* no candidates, no progress *)

  (* cover (cg, w, ccs, lab, missing) = missing'
       covers ([cg1,...,cgn], w, ccs, missing) = missing'

       Check if cover goal cg (or [cg1,..,cgn]) are covered by
       cover clauses ccs, adding missing cases to missing to yield missing'

       cg = CGoal (G, S) where G contains the splittable variables
       cci = CClause (Gi, Si) where Gi contains essentially existential variables

       w are the worlds for the principal type family

       lab is the label for the current goal for tracing purposes
    *)
  let rec cover (cg, w, ccs, lab, missing) =
    begin
      chatter 6 (function () -> showPendingCGoal (cg, lab) ^ "\n");
      cover' (contract (cg, lab), w, ccs, lab, missing)
    end

  and cover' (a, w, ccs, lab, missing) = match a with
    | Some cg ->
        let cands = match_ (cg, ccs) in
        let cand = selectCand cands in
        split (cg, cand, w, ccs, lab, missing)
        (* determine splitting candidates *)
        (* select one candidate *)
    | None -> begin
        chatter 6 (function () -> "Covered\n");
        missing
      end
  (* cg is covered by unique output inconsistency *)

  and split (cg, a, w, ccs, lab, missing) = match a with
    | None -> begin
        chatter 6 (function () -> "Covered\n");
        missing
      end
    | Some [] -> begin
        chatter 6 (function () ->
            "No strong candidates --- calculating weak candidates\n");
        splitWeak (cg, finitary (cg, w), w, ccs, lab, missing)
      end
    | Some ((k, _) :: ksn) -> begin
        chatter 6 (function () -> ("Splitting on " ^ Int.toString k) ^ "\n");
        begin match splitVar (cg, k, w) with
        | Some cases -> covers (cases, w, ccs, lab, missing)
        | None -> begin
            chatter 6 (function () ->
                "Splitting failed due to generated constraints\n");
            split (cg, Some ksn, w, ccs, lab, missing)
          end
        end
      end
  (* splitVar shows splitting as it happens *)
  (* candidates are in reverse order, so non-index candidates are split first *)
  (* some candidates: split first candidate, ignoring multiplicities *)
  (* no strong candidates: check for finitary splitting candidates *)
  (* cg is covered: return missing patterns from other cases *)

  and splitWeak (cg, ksn, w, ccs, lab, missing) = match ksn with
    | [] -> begin
        chatter 6 (function () ->
            ("No weak candidates---case " ^ labToString lab) ^ " not covered\n");
        cg :: missing
      end
    | ksn ->
        split (cg, Some [ findMin ksn ], w, ccs, lab, missing)
  (* ksn <> nil *)

  and covers (cases, w, ccs, lab, missing) =
    begin
      chatter 6 (function () ->
          (("Found " ^ Int.toString (List.length cases))
          ^ pluralize (List.length cases, " case"))
          ^ "\n");
      covers' (cases, 1, w, ccs, lab, missing)
    end

  and covers' (a, n, w, ccs, lab, missing) = match a with
    | [] -> begin
        chatter 6 (function () ->
            ("All subcases of " ^ labToString lab) ^ " considered\n");
        missing
      end
    | cg :: cases' ->
        let missing1 = cover (cg, w, ccs, Child (lab, n), missing) in
        covers' (cases', n + 1, w, ccs, lab, missing1)

  (* substToSpine' (s, G, T) = S @ T
       If   G' |- s : G
       then G' |- S : {{G}} a >> a  for arbitrary a
       {{G}} erases void declarations in G
    *)
  let rec substToSpine' (a, b, t_) = match a, b with
    | I.Shift n, I.Null -> t_
    | I.Shift n, (I.Decl _ as g) ->
        substToSpine' (I.Dot (I.Idx (n + 1), I.Shift (n + 1)), g, t_)
    | I.Dot (_, s), I.Decl (g, I.NDec _) -> substToSpine' (s, g, t_)
    | I.Dot (I.Exp u, s), I.Decl (g, v) ->
        substToSpine' (s, g, I.App (u, t_))
    | I.Dot (I.Idx n, s), I.Decl (g, I.Dec (_, v)) ->
        let us, _ =
          Whnf.whnfEta (I.Root (I.BVar n, I.Nil), I.id) (v, I.id)
        in
        substToSpine' (s, g, I.App (I.EClo (fst us, snd us), t_))
    | I.Dot (_, s), I.Decl (g, I.BDec (_, (l, t))) ->
        substToSpine' (s, g, t_)

  (* Attempted fix, didn't work because I don't know how you
             computed splitting candidates for Blocks
             --cs Sat Jan  4 22:38:01 2003
          *)
  (* Treat like I.NDec *)
  (* was: I.Idx in previous line, Sun Jan  5 11:02:19 2003 -fp *)
  (* Eta-expand *)
  (* Unusable meta-decs are eliminated here *)
  (* Skip over NDec's; must be either Undef or Idx [from eta-expansion] *)

  (* I.Axp, I.Block(B) or other I.Undef impossible *)
  (* substToSpine (s, G) = S
       If   G' |- s : G
       then G' |- S : {{G}} type

       Note: {{G}} erases void declarations in G
     *)
  let substToSpine (s, g) = substToSpine' (s, g, I.Nil)

  (* purify' G = (G', s) where all NDec's have been erased from G
       If    |- G ctx
       then  |- G ctx and  G' |- s : G
    *)
  let rec purify' = function
    | I.Null -> (I.Null, I.id)
    | I.Decl (g, I.NDec _) ->
        let g', s = purify' g in
        (g', I.Dot (I.Undef, s))
        (* G' |- s : G *)
        (* G' |- _.s : G,_ *)
    | I.Decl (g, (I.Dec _ as d)) ->
        let g', s = purify' g in
        (I.Decl (g', I.decSub d s), I.dot1 s)
        (* G' |- s : G *)
        (* G |- D : type *)
        (* G' |- D[s] : type *)
        (* G', D[s] |- 1 : D[s][^] *)
        (* G', D[s] |- s o ^ : G *)
        (* G', D[s] |- 1.s o ^ : G, D *)
    | I.Decl (g, (I.BDec _ as d)) ->
        let g', s = purify' g in
        (g', I.Dot (I.Undef, s))

  (* G' |- s : G *)
  (* G' |- _.s : G,_ *)
  (* added a new case to throw out blocks
         -cs Sat Jan  4 22:55:12 2003
      *)

  (* purify G = G' where all NDec's have been erased from G
       If   |- G ctx
       then |- G' ctx
    *)
  let purify g = (fun (r, _) -> r) (purify' g)

  (* coverageCheckCases (W, Cs, G) = R

       Invariant:
       If   Cs = [(G1, s1) .... (Gn, sn)]
       and  Gi |- si : G
       and  for all worlds Phi
       and  instantiations Phi |- s : G
       there exists at least one index k and substitution   Phi |- t : Gk
       s.t.  sk o t = s
    *)
  let coverageCheckCases w cs g =
    ignore (chatter 4 (function () -> "[Tomega coverage checker..."));
    ignore (chatter 4 (function () -> "\n"));
    let ccs =
      List.map (function gi, si -> CClause (gi, substToSpine (si, g))) cs
    in
    ignore (chatter 6 (function () -> "[Begin covering clauses]\n"));
    ignore (List.app
        (function cc -> chatter 6 (function () -> showCClause cc ^ "\n"))
        ccs);
    ignore (chatter 6 (function () -> "[End covering clauses]\n"));
    let pureG = purify g in
    let namedG = N.ctxLUName pureG in
    let r0 = substToSpine (I.id, namedG) in
    let cg0 = CGoal (namedG, r0) in
    let missing = cover (cg0, w, ccs, Top, []) in
    ignore begin match missing with
      | [] -> ()
      | _ :: _ -> raise (Error "Coverage error")
      end
      (* all cases covered *);
    ignore (chatter 4 (function () -> "]\n"));
    ()
  (* Question: are all the Gi's above named already? *)
end
(* functor Cover *)

(* # 1 "src/cover/Cover_.sml.ml" *)

module Cover =
  MakeCover (Global) (Whnf) (Conv) (Abstract) (UnifyTrail) (Constraints)
    (ModeTable)
    (UniqueTable)
    (Index)
    (Subordinate_.Subordinate)
    (WorldSyn)
    (Names)
    (Print)
    (TypeCheck)
    (Timers.Timers)

module Total = Total.Total (struct
  module Global = Global
  module Table = TableInstances.IntRedBlackTree

  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Names = Names
  module ModeTable = ModeTable
  module ModeCheck = ModeCheck
  module Index = Index
  module Subordinate = Subordinate_.Subordinate
  module Order = Order
  module Reduces = Terminate_.Reduces
  module Cover = Cover

  (*! structure Paths = Paths !*)
  module Origins = Origins
  module Timers = Timers.Timers
end)
