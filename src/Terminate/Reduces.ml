open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Formatter__Formatter_
open! Index.Index_
open! Paths
open! Paths.Paths_

(* # 1 "src/terminate/Reduces.sig.ml" *)

(* Reduction and Termination checker *)
(* Author: Brigitte Pientka *)
include REDUCES
(* signature REDUCES *)

(* # 1 "src/terminate/Reduces.fun.ml" *)
open! Basis

(* Reduction and Termination checker *)
(* Author: Brigitte Pientka *)
(* for termination checking see [Rohwedder,Pfenning ESOP'96]
   for a revised version incorporating reducation checking see
   tech report CMU-CS-01-115
 *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Reduces (Reduces__0 : sig
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module Formatter : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn' !*)
  (*! structure Paths  : PATHS !*)
  module Checking : Checking.CHECKING

  (*! sharing Checking.IntSyn = IntSyn' !*)
  (*! sharing Checking.Paths = Paths !*)
  module Origins : Origins.ORIGINS
end) : REDUCES = struct
  (*! structure IntSyn = IntSyn' !*)
  exception Error = Error

  open! struct
    module I = IntSyn
    module P = Paths
    module N = Names
    module F = Print.Formatter
    module C = Reduces__0.Checking
    module R = C.Order

    exception Error' of P.occ * string

    let error (c, occ, msg) =
      begin match Origins.originLookup c with
      | fileName, None -> raise (Error ((fileName ^ ":") ^ msg))
      | fileName, Some occDec ->
          raise
            (Error
               (P.wrapLoc'
                  (P.Loc (fileName, P.occToRegionDec occDec occ)) (Origins.linesInfoLookup fileName) msg))
      end

    let rec concat (g', a) = match a with
      | I.Null -> g'
      | I.Decl (g, d) -> I.Decl (concat (g', g), d)

    let fmtOrder (g, o) =
      let rec fmtOrder' = function
        | R.Arg (((u, s) as us), ((v, s') as vs)) ->
            F.hbox
              [
                F.string "(";
                Print.formatExp g (I.EClo (fst us, snd us));
                F.string ")";
              ]
        | R.Lex l ->
            F.hbox
              [ F.string "{"; F.hOVbox0 1 0 1 (fmtOrders l); F.string "}" ]
        | R.Simul l ->
            F.hbox
              [ F.string "["; F.hOVbox0 1 0 1 (fmtOrders l); F.string "]" ]
      and fmtOrders = function
        | [] -> []
        | o :: [] -> [ fmtOrder' o ]
        | o :: l -> fmtOrder' o :: F.break :: fmtOrders l
      in
      fmtOrder' o

    let fmtComparison (g, o, comp, o') =
      F.hOVbox0 1 0 1
        [
          fmtOrder (g, o); F.break; F.string comp; F.break; fmtOrder (g, o');
        ]

    let rec fmtPredicate (g, a) = match a with
      | C.Less (o, o') -> fmtComparison (g, o, "<", o')
      | C.Leq (o, o') -> fmtComparison (g, o, "<=", o')
      | C.Eq (o, o') -> fmtComparison (g, o, "=", o')
      | C.Pi (d, p) ->
          F.hbox [ F.string "Pi "; fmtPredicate (I.Decl (g, d), p) ]

    let rec rlistToString' (g, a) = match a with
      | [] -> ""
      | p :: [] -> F.makestring_fmt (fmtPredicate (g, p))
      | p :: rl ->
          (F.makestring_fmt (fmtPredicate (g, p)) ^ " ,")
          ^ rlistToString' (g, rl)

    let rlistToString (g, rl) = rlistToString' (Names.ctxName g, rl)

    let orderToString (g, p) =
      F.makestring_fmt (fmtPredicate (Names.ctxName g, p))

    let select (c, (s_, s)) =
      let so = R.selLookup c in
      let vid : I.eclo = (I.constType c, I.id) in
      let rec select'' (n, (ss', vs'')) : I.eclo * I.eclo =
        select''W (n, (ss', Whnf.whnf vs''))
      and select''W = function
        | 1, ((I.App (u', s'_), s'), (I.Pi ((I.Dec (_, v''), _), _), s'')) ->
            ((u', s'), (v'', s''))
        | n, ((I.SClo (s', s1'), s2'), vs'') ->
            select''W (n, ((s', I.comp s1' s2'), vs''))
        | n, ((I.App (u', s'_), s'), (I.Pi ((I.Dec (_, v1''), _), v2''), s''))
          ->
            select''
              (n - 1, ((s'_, s'), (v2'', I.Dot (I.Exp (I.EClo (u', s')), s''))))
      in
      let rec select' = function
        | R.Arg n -> R.Arg (select'' (n, ((s_, s), vid)))
        | R.Lex l -> R.Lex (map select' l)
        | R.Simul l -> R.Simul (map select' l)
      in
      select' (R.selLookup c)

    let selectOcc (c, (s_, s), occ) =
      try select (c, (s_, s))
      with R.Error msg ->
        raise
          (Error'
             ( occ,
               "Termination violation: no order assigned for "
               ^ N.qidToString (N.constQid c) ))

    let selectROrder (c, (s_, s)) =
      let vid : I.eclo = (I.constType c, I.id) in
      let rec select'' (n, (ss', vs'')) : I.eclo * I.eclo =
        select''W (n, (ss', Whnf.whnf vs''))
      and select''W = function
        | 1, ((I.App (u', s'_), s'), (I.Pi ((I.Dec (_, v''), _), _), s'')) ->
            ((u', s'), (v'', s''))
        | n, ((I.SClo (s', s1'), s2'), vs'') ->
            select''W (n, ((s', I.comp s1' s2'), vs''))
        | n, ((I.App (u', s'_), s'), (I.Pi ((I.Dec (_, v1''), _), v2''), s''))
          ->
            select''
              (n - 1, ((s'_, s'), (v2'', I.Dot (I.Exp (I.EClo (u', s')), s''))))
      in
      let rec select' = function
        | R.Arg n -> R.Arg (select'' (n, ((s_, s), vid)))
        | R.Lex l -> R.Lex (map select' l)
        | R.Simul l -> R.Simul (map select' l)
      in
      let selectP = function
        | R.Less (o1, o2) -> C.Less (select' o1, select' o2)
        | R.Leq (o1, o2) -> C.Leq (select' o1, select' o2)
        | R.Eq (o1, o2) -> C.Eq (select' o1, select' o2)
      in
      try Some (selectP (R.selLookupROrder c)) with R.Error s -> None

    let abstractRO (g, d, o) = C.Pi (d, o)

    let rec getROrder (g, q, vs, occ) =
      getROrderW (g, q, Whnf.whnf vs, occ)

    and getROrderW (g, q, b, occ) = match b with
      | ((I.Root (I.Const a, s_), s) as vs) ->
          let o = selectROrder (a, (s_, s)) in
          ignore begin match o with
            | None -> ()
            | Some o ->
                begin if !Global.chatter > 5 then
                  print
                    (((("Reduction predicate for "
                       ^ N.qidToString (N.constQid a))
                      ^ " added : ")
                     ^ orderToString (g, o))
                    ^ "\n")
                else ()
                end
            end;
          o
      | (I.Pi ((d, Maybe), v), s) ->
          let o =
            getROrder
              ( I.Decl (g, N.decLUName g (I.decSub d s)),
                I.Decl (q, C.All),
                (v, I.dot1 s),
                P.body occ )
          in
          begin match o with
          | None -> None
          | Some o' -> Some (abstractRO (g, I.decSub d s, o'))
          end
      | (I.Pi (((I.Dec (_, v1) as d), No), v2), s) ->
          let o =
            getROrder (g, q, (v2, I.comp I.invShift s), P.body occ)
          in
          begin match o with None -> None | Some o' -> Some o'
          end
      | ((I.Root (I.Def a, s_), s) as vs) ->
          raise
            (Error'
               ( occ,
                 (("Reduction checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a))
                 ^ "." ))

    let rec checkGoal (g0, q0, rl, vs, vs', occ) =
      checkGoalW (g0, q0, rl, Whnf.whnf vs, vs', occ)

    and checkGoalW (g0, q0, rl, b, c, occ) = match b, c with
      | (I.Pi (((I.Dec (_, v1) as d), No), v2), s), vs'
        -> begin
          checkClause ((g0, q0, rl), I.Null, I.Null, (v1, s), P.label occ);
          checkGoal
            (g0, q0, rl, (v2, I.comp I.invShift s), vs', P.body occ)
        end
      | (I.Pi ((d, Maybe), v), s), (v', s') ->
          checkGoal
            ( I.Decl (g0, N.decLUName g0 (I.decSub d s)),
              I.Decl (q0, C.All),
              C.shiftRCtx rl (function s -> I.comp s I.shift),
              (v, I.dot1 s),
              (v', I.comp s' I.shift),
              P.body occ )
      | ((I.Root (I.Const a, s_), s) as vs), ((I.Root (I.Const a', s'_), s') as vs') ->
          let rec lookup (b, f) = match b with
            | R.Empty -> R.Empty
            | (R.Le (a, a's') as a's) ->
                begin if f a then a's else lookup (a's', f)
                end
            | (R.Lt (a, a's') as a's) ->
                begin if f a then a's else lookup (a's', f)
                end
          in
          let p : (I.eclo * I.eclo) R.order = selectOcc (a, (s_, s), occ) in
          let p' : (I.eclo * I.eclo) R.order = select (a', (s'_, s')) in
          let a's = R.mutLookup a in
          begin match lookup (a's, function x' -> x' = a') with
          | R.Empty -> ()
          | R.Le _ -> begin
              begin if !Global.chatter > 4 then begin
                print "Verifying termination order:\n";
                begin
                  print (rlistToString (g0, rl));
                  print
                    ((" ---> " ^ orderToString (g0, C.Leq (p, p'))) ^ "\n")
                end
              end
              else ()
              end;
              begin if C.deduce g0 q0 rl (C.Leq (p, p')) then ()
              else
                raise
                  (Error'
                     ( occ,
                       (("Termination violation:\n" ^ rlistToString (g0, rl))
                       ^ " ---> ")
                       ^ orderToString (g0, C.Leq (p, p')) ))
              end
            end
          | R.Lt _ -> begin
              begin if !Global.chatter > 4 then begin
                print "Verifying termination order:\n";
                begin
                  print (rlistToString (g0, rl) ^ " ---> ");
                  print (orderToString (g0, C.Less (p, p')) ^ "\n")
                end
              end
              else ()
              end;
              begin if C.deduce g0 q0 rl (C.Less (p, p')) then ()
              else
                raise
                  (Error'
                     ( occ,
                       (("Termination violation:\n" ^ rlistToString (g0, rl))
                       ^ " ---> ")
                       ^ orderToString (g0, C.Less (p, p')) ))
              end
            end
          end
      | ((I.Root (I.Def a, s_), s) as vs), vs' ->
          raise
            (Error'
               ( occ,
                 (("Reduction checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a))
                 ^ "." ))
      | vs, ((I.Root (I.Def a', s'_), s') as vs') ->
          raise
            (Error'
               ( occ,
                 (("Reduction checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a'))
                 ^ "." ))

    and checkSubgoals (g0, q0, rl, vs, n, a) = match a with
      | (I.Decl (g, (I.Dec (_, v') as d)), I.Decl (q, C.And occ)) ->
          ignore (checkGoal (g0, q0, rl, (v', I.Shift (n + 1)), vs, occ));
          let ro = getROrder (g0, q0, (v', I.Shift (n + 1)), occ) in
          let rl' =
            begin match ro with None -> rl | Some o -> o :: rl
            end
          in
          checkSubgoals (g0, q0, rl', vs, n + 1, (g, q))
      | (I.Decl (g, d), I.Decl (q, C.Exist)) ->
          checkSubgoals (g0, q0, rl, vs, n + 1, (g, q))
      | (I.Decl (g, d), I.Decl (q, C.All)) ->
          checkSubgoals (g0, q0, rl, vs, n + 1, (g, q))
      | (_, _) -> ()

    and checkClause (gqr, g, q, vs, occ) =
      checkClauseW (gqr, g, q, Whnf.whnf vs, occ)

    and checkClauseW (b, g, q, c, occ) = match b, c with
      | gqr, (I.Pi ((d, Maybe), v), s) ->
          checkClause
            ( gqr,
              I.Decl (g, N.decEName g (I.decSub d s)),
              I.Decl (q, C.Exist),
              (v, I.dot1 s),
              P.body occ )
      | gqr, (I.Pi (((I.Dec (_, v1) as d), No), v2), s) ->
          checkClause
            ( gqr,
              I.Decl (g, I.decSub d s),
              I.Decl (q, C.And (P.label occ)),
              (v2, I.dot1 s),
              P.body occ )
      | ((g0, q0, rl) as gqr), ((I.Root (I.Const a, s_), s) as vs) ->
          let n = I.ctxLength g in
          let rl' = C.shiftRCtx rl (function s -> I.comp s (I.Shift n)) in
          checkSubgoals
            (concat (g0, g), concat (q0, q), rl', vs, 0, (g, q))
      | gqr, (I.Root (I.Def a, s_), s) ->
          raise
            (Error'
               ( occ,
                 (("Termination checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a))
                 ^ "." ))

    let checkClause' (vs, occ) =
      checkClause ((I.Null, I.Null, []), I.Null, I.Null, vs, occ)

    let rec checkRGoal (g, q, rl, vs, occ) =
      checkRGoalW (g, q, rl, Whnf.whnf vs, occ)

    and checkRGoalW (g, q, rl, b, occ) = match b with
      | ((I.Root (I.Const a, s_), s) as vs) -> ()
      | (I.Pi ((d, Maybe), v), s) ->
          checkRGoal
            ( I.Decl (g, N.decLUName g (I.decSub d s)),
              I.Decl (q, C.All),
              C.shiftRCtx rl (function s -> I.comp s I.shift),
              (v, I.dot1 s),
              P.body occ )
      | (I.Pi (((I.Dec (_, v1) as d), No), v2), s) -> begin
          checkRClause (g, q, rl, (v1, s), P.label occ);
          checkRGoal (g, q, rl, (v2, I.comp I.invShift s), P.body occ)
        end
      | (I.Root (I.Def a, s_), s) ->
          raise
            (Error'
               ( occ,
                 (("Reduction checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a))
                 ^ "." ))

    and checkRImp (g, q, rl, vs, vs', occ) =
      checkRImpW (g, q, rl, Whnf.whnf vs, vs', occ)

    and checkRImpW (g, q, rl, b, vs, occ) = match b, vs with
      | (I.Pi ((d', Maybe), v'), s'), (v, s) ->
          checkRImp
            ( I.Decl (g, N.decEName g (I.decSub d' s')),
              I.Decl (q, C.Exist),
              C.shiftRCtx rl (function s -> I.comp s I.shift),
              (v', I.dot1 s'),
              (v, I.comp s I.shift),
              occ )
      | (I.Pi (((I.Dec (_, v1) as d'), No), v2), s'), (v, s) ->
          let rl' =
            begin match getROrder (g, q, (v1, s'), occ) with
            | None -> rl
            | Some o -> o :: rl
            end
          in
          checkRImp (g, q, rl', (v2, I.comp I.invShift s'), (v, s), occ)
      | ((I.Root (I.Const a, s_), s) as vs'), vs ->
          checkRGoal (g, q, rl, vs, occ)
      | ((I.Root (I.Def a, s_), s) as vs'), vs ->
          raise
            (Error'
               ( occ,
                 (("Reduction checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a))
                 ^ "." ))

    and checkRClause (g, q, rl, vs, occ) =
      checkRClauseW (g, q, rl, Whnf.whnf vs, occ)

    and checkRClauseW (g, q, rl, b, occ) = match b with
      | (I.Pi ((d, Maybe), v), s) ->
          checkRClause
            ( I.Decl (g, N.decEName g (I.decSub d s)),
              I.Decl (q, C.Exist),
              C.shiftRCtx rl (function s -> I.comp s I.shift),
              (v, I.dot1 s),
              P.body occ )
      | (I.Pi (((I.Dec (_, v1) as d), No), v2), s) ->
          let g' = I.Decl (g, I.decSub d s) in
          let q' = I.Decl (q, C.Exist) in
          let rl' = C.shiftRCtx rl (function s -> I.comp s I.shift) in
          let rl'' =
            begin match
              getROrder (g', q', (v1, I.comp s I.shift), occ)
            with
            | None -> rl'
            | Some o -> o :: rl'
            end
          in
          checkRClause (g', q', rl'', (v2, I.dot1 s), P.body occ);
          checkRImp
            ( g',
              q',
              rl'',
              (v2, I.dot1 s),
              (v1, I.comp s I.shift),
              P.label occ )
      | ((I.Root (I.Const a, s_), s) as vs) ->
          let ro =
            begin match selectROrder (a, (s_, s)) with
            | None ->
                raise
                  (Error'
                     ( occ,
                       ("No reduction order assigned for "
                       ^ N.qidToString (N.constQid a))
                       ^ "." ))
            | Some o -> o
            end
          in
          ignore begin if !Global.chatter > 4 then
              print
                (((("Verifying reduction property:\n" ^ rlistToString (g, rl))
                  ^ " ---> ")
                 ^ orderToString (g, ro))
                ^ " \n")
            else ()
            end;
          begin if C.deduce g q rl ro then ()
          else
            raise
              (Error'
                 ( occ,
                   (("Reduction violation:\n" ^ rlistToString (g, rl))
                   ^ " ---> ")
                   ^ orderToString (g, ro) ))
          end
      | ((I.Root (I.Def a, s_), s) as vs) ->
          raise
            (Error'
               ( occ,
                 (("Reduction checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a))
                 ^ "." ))

    let checkFamReduction a =
      let rec checkFam' = function
        | [] -> begin
            begin if !Global.chatter > 3 then print "\n" else ()
            end;
            ()
          end
        | I.Const b :: bs -> begin
            begin if !Global.chatter > 3 then
              print (N.qidToString (N.constQid b) ^ " ")
            else ()
            end;
            begin
              begin if !Global.chatter > 4 then begin
                N.varReset IntSyn.Null;
                print "\n"
              end
              else ()
              end;
              begin try
                checkRClause (I.Null, I.Null, [], (I.constType b, I.id), P.top)
              with
              | Error' (occ, msg) -> error (b, occ, msg)
              | R.Error msg ->
                  raise (Error msg);
                  checkFam' bs
              end
            end
          end
        | I.Def d :: bs -> begin
            begin if !Global.chatter > 3 then
              print (N.qidToString (N.constQid d) ^ " ")
            else ()
            end;
            begin
              begin if !Global.chatter > 4 then begin
                N.varReset IntSyn.Null;
                print "\n"
              end
              else ()
              end;
              begin try
                checkRClause (I.Null, I.Null, [], (I.constType d, I.id), P.top)
              with
              | Error' (occ, msg) -> error (d, occ, msg)
              | R.Error msg ->
                  raise (Error msg);
                  checkFam' bs
              end
            end
          end
      in
      ignore begin if !Global.chatter > 3 then
          print
            (("Reduction checking family " ^ N.qidToString (N.constQid a))
            ^ ":\n")
        else ()
        end;
      checkFam' (Index.lookup a)

    let checkFam a =
      let rec checkFam' = function
        | [] -> begin
            begin if !Global.chatter > 3 then print "\n" else ()
            end;
            ()
          end
        | I.Const b :: bs -> begin
            begin if !Global.chatter > 3 then
              print (N.qidToString (N.constQid b) ^ " ")
            else ()
            end;
            begin
              begin if !Global.chatter > 4 then begin
                N.varReset IntSyn.Null;
                print "\n"
              end
              else ()
              end;
              begin try checkClause' ((I.constType b, I.id), P.top) with
              | Error' (occ, msg) -> error (b, occ, msg)
              | R.Error msg ->
                  raise (Error msg);
                  checkFam' bs
              end
            end
          end
        | I.Def d :: bs -> begin
            begin if !Global.chatter > 3 then
              print (N.qidToString (N.constQid d) ^ " ")
            else ()
            end;
            begin
              begin if !Global.chatter > 4 then begin
                N.varReset IntSyn.Null;
                print "\n"
              end
              else ()
              end;
              begin try checkClause' ((I.constType d, I.id), P.top) with
              | Error' (occ, msg) -> error (d, occ, msg)
              | R.Error msg ->
                  raise (Error msg);
                  checkFam' bs
              end
            end
          end
      in
      ignore begin if !Global.chatter > 3 then
          print
            (("Termination checking family " ^ N.qidToString (N.constQid a))
            ^ "\n")
        else ()
        end;
      checkFam' (Index.lookup a)

    let reset () =
      begin
        R.reset ();
        R.resetROrder ()
      end
  end

  (*--------------------------------------------------------------------*)
  (* Printing *)
  (*--------------------------------------------------------------------*)
  (* select (c, (S, s)) = P

      select parameters according to termination order

      Invariant:
      If   . |- c : V   G |- s : G'    G' |- S : V > type
      and  V = {x1:V1} ... {xn:Vn} type.
      then P = U1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
      and  G |- si : Gi  Gi |- Ui : Vi
      and  G |- Vi[s]  == V[si] : type   forall 1<=i<=n
    *)
  (* selectROrder (c, (S, s)) = P

       select parameters according to reduction order

       Invariant:
       If   . |- c : V   G |- s : G'    G' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type.
       then P = U1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
       and  G |- si : Gi  Gi |- Ui : Vi
       and  G |- Vi[s]  == V[si] : type   forall 1<=i<=n
    *)
  (*--------------------------------------------------------------*)
  (* abstractRO (G, D, RO) = Pi D. RO
       Invariant:

       If  G, D |- RO
       then  G |- Pi D . RO

    *)
  (* getROrder (G, Q, (V, s)) = O
       If G: Q
       and  G |- s : G1    and   G1 |- V : L
       then O is the reduction order associated to V[s]
       and  G |- O

     *)
  (*--------------------------------------------------------------------*)
  (* Termination Checker *)
  (* checkGoal (G0, Q0, Rl, (V, s), (V', s'), occ) = ()

       Invariant:
       If   G0 : Q0
       and  G0 |- s : G1     and   G1 |- V : L     (V, s) in whnf
       and  V[s], V'[s'] does not contain Skolem constants
       and  G0 |- s' : G2    and   G2 |- V' : L'   (V', s') in whnf
       and  V' = a' @ S'
       and  G |- L = L'
       and  V[s] < V'[s']  (< termination ordering)
         then ()
       else Error is raised.
    *)
  (* only if a terminates? *)
  (* always succeeds? -fp *)
  (* always succeeds? -fp *)
  (* checkSubgoals (G0, Q0, Rl, Vs, n, (G, Q), Vs, occ)

      if    G0 |- Q0
       and  G0 |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any skolem constants
       and  Rl is a list of reduction propositions
       and  G0 |- Rl
       and  G0 |- V[s]
       and  G0 = G0', G' where G' <= G
       and  n = |G'| - |G|
       and  G0 |- G[^n]
       and  G |- Q
     and
       V[s] satisfies the associated termination order

     *)
  (* checkClause (GQR as (G0, Q0, Rl), G, Q, Vs, occ)

      if   G0, G |- Q0, Q
       and  G0, G |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any skolem constants
       and  Rl is a list of reduction propositions
       and  G0, G |- Rl
       and  G0, G |- V[s]
     and
       V[s] satisfies the associated termination order
     *)
  (*-------------------------------------------------------------------*)
  (* Reduction Checker *)
  (* checkRGoal (G, Q, Rl, (V1, s1), occ) = Rl''

       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and Rl is a context of reduction predicates
       and  G |- Rl
       and Rl implies that V1[s1] satisfies its associated reduction order

     *)
  (* trivial *)
  (* checkRImp (G, Q, Rl, (V1, s1), (V2, s2), occ) = ()

       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and Rl is a context for derived reduction order assumptions
       and G |- Rl

       then Rl implies that  V2[s2] satisfies its associated reduction order
            with respect to V1[s1]
    *)
  (* checkRClause (G, Q, Rl, (V, s)) = ()

       Invariant:
       If G: Q
       and  G |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any Skolem constants
       and  Rl is a context of reduction predicates
       and  G |- Rl
       then Rl implies that V[s] satifies the reduction order
    *)
  (* N.decEName (G, I.decSub (D, s)) *)
  (* will not be used *)
  (* rename ctx ??? *)
  (* checkFamReduction a = ()

       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for a does not fulfill
       specified reducation property

       Note: checking reduction is a separate property of termination
    *)
  (* reuse variable names when tracing *)
  (* reuse variable names when tracing *)
  (* checkFam a = ()

       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for a do not terminate
       according to specified termination order

       Note: termination checking takes into account proven
             reduction properties.
    *)
  (* reuse variable names when tracing *)
  (* reuse variable names when tracing *)
  let reset = reset
  let checkFamReduction = checkFamReduction
  let checkFam = checkFam
end
(*! sharing Origins.Paths = Paths !*)
(*! sharing Origins.IntSyn = IntSyn' !*)
(*! structure CsManager : CS_MANAGER !*)
(*! sharing CsManager.IntSyn = IntSyn' !*)
(* local *)
(* functor Reduces  *)

(* # 1 "src/terminate/Reduces.sml.ml" *)
