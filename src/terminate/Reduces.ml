(* # 1 "src/terminate/Reduces.sig.ml" *)
open! Basis

(* Reduction and Termination checker *)
(* Author: Brigitte Pientka *)
include Reduces_intf
(* signature REDUCES *)

(* # 1 "src/terminate/Reduces.fun.ml" *)
open! Basis

(* Reduction and Termination checker *)
(* Author: Brigitte Pientka *)
(* for termination checking see [Rohwedder,Pfenning ESOP'96]
   for a revised version incorporating reducation checking see
   tech report CMU-CS-01-115
 *)
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
  exception Error of string

  open! struct
    module I = IntSyn
    module P = Paths
    module N = Names
    module F = Print.Formatter
    module C = Reduces__0.Checking
    module R = C.Order

    exception Error' of P.occ * string

    let rec error (c, occ, msg) =
      begin match Origins.originLookup c with
      | fileName, None -> raise (Error ((fileName ^ ":") ^ msg))
      | fileName, Some occDec ->
          raise
            (Error
               (P.wrapLoc'
                  ( P.Loc (fileName, P.occToRegionDec occDec occ),
                    Origins.linesInfoLookup fileName,
                    msg )))
      end

    let rec concat = function
      | g'_, I.Null -> g'_
      | g'_, I.Decl (g_, d_) -> I.Decl (concat (g'_, g_), d_)

    let rec fmtOrder (g_, o_) =
      let rec fmtOrder' = function
        | R.Arg (((u_, s) as us_), ((v_, s') as vs_)) ->
            F.hbox
              [
                F.string "(";
                Print.formatExp (g_, I.EClo (fst us_, snd us_));
                F.string ")";
              ]
        | R.Lex l_ ->
            F.hbox
              [ F.string "{"; F.hOVbox0 1 0 1 (fmtOrders l_); F.string "}" ]
        | R.Simul l_ ->
            F.hbox
              [ F.string "["; F.hOVbox0 1 0 1 (fmtOrders l_); F.string "]" ]
      and fmtOrders = function
        | [] -> []
        | o_ :: [] -> [ fmtOrder' o_ ]
        | o_ :: l_ -> fmtOrder' o_ :: F.break :: fmtOrders l_
      in
      fmtOrder' o_

    let rec fmtComparison (g_, o_, comp, o'_) =
      F.hOVbox0 1 0 1
        [
          fmtOrder (g_, o_); F.break; F.string comp; F.break; fmtOrder (g_, o'_);
        ]

    let rec fmtPredicate = function
      | g_, C.Less (o_, o'_) -> fmtComparison (g_, o_, "<", o'_)
      | g_, C.Leq (o_, o'_) -> fmtComparison (g_, o_, "<=", o'_)
      | g_, C.Eq (o_, o'_) -> fmtComparison (g_, o_, "=", o'_)
      | g_, C.Pi (d_, p_) ->
          F.hbox [ F.string "Pi "; fmtPredicate (I.Decl (g_, d_), p_) ]

    let rec rlistToString' = function
      | g_, [] -> ""
      | g_, p_ :: [] -> F.makestring_fmt (fmtPredicate (g_, p_))
      | g_, p_ :: rl_ ->
          (F.makestring_fmt (fmtPredicate (g_, p_)) ^ " ,")
          ^ rlistToString' (g_, rl_)

    let rec rlistToString (g_, rl_) = rlistToString' (Names.ctxName g_, rl_)

    let rec orderToString (g_, p_) =
      F.makestring_fmt (fmtPredicate (Names.ctxName g_, p_))

    let rec select (c, (s_, s)) =
      let so_ = R.selLookup c in
      let vid_ : I.eclo = (I.constType c, I.id) in
      let rec select'' (n, (ss'_, vs''_)) : I.eclo * I.eclo =
        select''W (n, (ss'_, Whnf.whnf vs''_))
      and select''W = function
        | 1, ((I.App (u'_, s'_), s'), (I.Pi ((I.Dec (_, v''_), _), _), s'')) ->
            ((u'_, s'), (v''_, s''))
        | n, ((I.SClo (s'_, s1'), s2'), vs''_) ->
            select''W (n, ((s'_, I.comp (s1', s2')), vs''_))
        | n, ((I.App (u'_, s'_), s'), (I.Pi ((I.Dec (_, v1''_), _), v2''_), s''))
          ->
            select''
              ( n - 1,
                ((s'_, s'), (v2''_, I.Dot (I.Exp (I.EClo (u'_, s')), s''))) )
      in
      let rec select' = function
        | R.Arg n -> R.Arg (select'' (n, ((s_, s), vid_)))
        | R.Lex l_ -> R.Lex (map select' l_)
        | R.Simul l_ -> R.Simul (map select' l_)
      in
      select' (R.selLookup c)

    let rec selectOcc (c, (s_, s), occ) =
      try select (c, (s_, s))
      with R.Error msg ->
        raise
          (Error'
             ( occ,
               "Termination violation: no order assigned for "
               ^ N.qidToString (N.constQid c) ))

    let rec selectROrder (c, (s_, s)) =
      let vid_ : I.eclo = (I.constType c, I.id) in
      let rec select'' (n, (ss'_, vs''_)) : I.eclo * I.eclo =
        select''W (n, (ss'_, Whnf.whnf vs''_))
      and select''W = function
        | 1, ((I.App (u'_, s'_), s'), (I.Pi ((I.Dec (_, v''_), _), _), s'')) ->
            ((u'_, s'), (v''_, s''))
        | n, ((I.SClo (s'_, s1'), s2'), vs''_) ->
            select''W (n, ((s'_, I.comp (s1', s2')), vs''_))
        | n, ((I.App (u'_, s'_), s'), (I.Pi ((I.Dec (_, v1''_), _), v2''_), s''))
          ->
            select''
              ( n - 1,
                ((s'_, s'), (v2''_, I.Dot (I.Exp (I.EClo (u'_, s')), s''))) )
      in
      let rec select' = function
        | R.Arg n -> R.Arg (select'' (n, ((s_, s), vid_)))
        | R.Lex l_ -> R.Lex (map select' l_)
        | R.Simul l_ -> R.Simul (map select' l_)
      in
      let rec selectP = function
        | R.Less (o1_, o2_) -> C.Less (select' o1_, select' o2_)
        | R.Leq (o1_, o2_) -> C.Leq (select' o1_, select' o2_)
        | R.Eq (o1_, o2_) -> C.Eq (select' o1_, select' o2_)
      in
      try Some (selectP (R.selLookupROrder c)) with R.Error s -> None

    let rec abstractRO (g_, d_, o_) = C.Pi (d_, o_)

    let rec getROrder (g_, q_, vs_, occ) =
      getROrderW (g_, q_, Whnf.whnf vs_, occ)

    and getROrderW = function
      | g_, q_, ((I.Root (I.Const a, s_), s) as vs_), occ ->
          let o_ = selectROrder (a, (s_, s)) in
          let _ =
            begin match o_ with
            | None -> ()
            | Some o_ -> begin
                if !Global.chatter > 5 then
                  print
                    (((("Reduction predicate for "
                       ^ N.qidToString (N.constQid a))
                      ^ " added : ")
                     ^ orderToString (g_, o_))
                    ^ "\n")
                else ()
              end
            end
          in
          o_
      | g_, q_, (I.Pi ((d_, Maybe), v_), s), occ ->
          let o_ =
            getROrder
              ( I.Decl (g_, N.decLUName (g_, I.decSub (d_, s))),
                I.Decl (q_, C.All),
                (v_, I.dot1 s),
                P.body occ )
          in
          begin match o_ with
          | None -> None
          | Some o'_ -> Some (abstractRO (g_, I.decSub (d_, s), o'_))
          end
      | g_, q_, (I.Pi (((I.Dec (_, v1_) as d_), No), v2_), s), occ ->
          let o_ =
            getROrder (g_, q_, (v2_, I.comp (I.invShift, s)), P.body occ)
          in
          begin match o_ with None -> None | Some o'_ -> Some o'_
          end
      | g_, q_, ((I.Root (I.Def a, s_), s) as vs_), occ ->
          raise
            (Error'
               ( occ,
                 (("Reduction checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a))
                 ^ "." ))

    let rec checkGoal (g0_, q0_, rl_, vs_, vs'_, occ) =
      checkGoalW (g0_, q0_, rl_, Whnf.whnf vs_, vs'_, occ)

    and checkGoalW = function
      | g0_, q0_, rl_, (I.Pi (((I.Dec (_, v1_) as d_), No), v2_), s), vs'_, occ
        -> begin
          checkClause ((g0_, q0_, rl_), I.Null, I.Null, (v1_, s), P.label occ);
          checkGoal
            (g0_, q0_, rl_, (v2_, I.comp (I.invShift, s)), vs'_, P.body occ)
        end
      | g0_, q0_, rl_, (I.Pi ((d_, Maybe), v_), s), (v'_, s'), occ ->
          checkGoal
            ( I.Decl (g0_, N.decLUName (g0_, I.decSub (d_, s))),
              I.Decl (q0_, C.All),
              C.shiftRCtx rl_ (function s -> I.comp (s, I.shift)),
              (v_, I.dot1 s),
              (v'_, I.comp (s', I.shift)),
              P.body occ )
      | ( g0_,
          q0_,
          rl_,
          ((I.Root (I.Const a, s_), s) as vs_),
          ((I.Root (I.Const a', s'_), s') as vs'_),
          occ ) ->
          let rec lookup = function
            | R.Empty, f -> R.Empty
            | (R.Le (a, a's') as a's), f -> begin
                if f a then a's else lookup (a's', f)
              end
            | (R.Lt (a, a's') as a's), f -> begin
                if f a then a's else lookup (a's', f)
              end
          in
          let p_ : (I.eclo * I.eclo) R.order = selectOcc (a, (s_, s), occ) in
          let p'_ : (I.eclo * I.eclo) R.order = select (a', (s'_, s')) in
          let a's = R.mutLookup a in
          begin match lookup (a's, function x' -> x' = a') with
          | R.Empty -> ()
          | R.Le _ -> begin
              begin if !Global.chatter > 4 then begin
                print "Verifying termination order:\n";
                begin
                  print (rlistToString (g0_, rl_));
                  print
                    ((" ---> " ^ orderToString (g0_, C.Leq (p_, p'_))) ^ "\n")
                end
              end
              else ()
              end;
              begin if C.deduce (g0_, q0_, rl_, C.Leq (p_, p'_)) then ()
              else
                raise
                  (Error'
                     ( occ,
                       (("Termination violation:\n" ^ rlistToString (g0_, rl_))
                       ^ " ---> ")
                       ^ orderToString (g0_, C.Leq (p_, p'_)) ))
              end
            end
          | R.Lt _ -> begin
              begin if !Global.chatter > 4 then begin
                print "Verifying termination order:\n";
                begin
                  print (rlistToString (g0_, rl_) ^ " ---> ");
                  print (orderToString (g0_, C.Less (p_, p'_)) ^ "\n")
                end
              end
              else ()
              end;
              begin if C.deduce (g0_, q0_, rl_, C.Less (p_, p'_)) then ()
              else
                raise
                  (Error'
                     ( occ,
                       (("Termination violation:\n" ^ rlistToString (g0_, rl_))
                       ^ " ---> ")
                       ^ orderToString (g0_, C.Less (p_, p'_)) ))
              end
            end
          end
      | g0_, q0_, rl_, ((I.Root (I.Def a, s_), s) as vs_), vs'_, occ ->
          raise
            (Error'
               ( occ,
                 (("Reduction checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a))
                 ^ "." ))
      | g0_, q0_, rl_, vs_, ((I.Root (I.Def a', s'_), s') as vs'_), occ ->
          raise
            (Error'
               ( occ,
                 (("Reduction checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a'))
                 ^ "." ))

    and checkSubgoals = function
      | ( g0_,
          q0_,
          rl_,
          vs_,
          n,
          (I.Decl (g_, (I.Dec (_, v'_) as d_)), I.Decl (q_, C.And occ)) ) ->
          let _ = checkGoal (g0_, q0_, rl_, (v'_, I.Shift (n + 1)), vs_, occ) in
          let ro_ = getROrder (g0_, q0_, (v'_, I.Shift (n + 1)), occ) in
          let rl'_ =
            begin match ro_ with None -> rl_ | Some o_ -> o_ :: rl_
            end
          in
          checkSubgoals (g0_, q0_, rl'_, vs_, n + 1, (g_, q_))
      | g0_, q0_, rl_, vs_, n, (I.Decl (g_, d_), I.Decl (q_, C.Exist)) ->
          checkSubgoals (g0_, q0_, rl_, vs_, n + 1, (g_, q_))
      | g0_, q0_, rl_, vs_, n, (I.Decl (g_, d_), I.Decl (q_, C.All)) ->
          checkSubgoals (g0_, q0_, rl_, vs_, n + 1, (g_, q_))
      | g0_, q0_, rl_, vs_, n, (_, _) -> ()

    and checkClause (gqr_, g_, q_, vs_, occ) =
      checkClauseW (gqr_, g_, q_, Whnf.whnf vs_, occ)

    and checkClauseW = function
      | gqr_, g_, q_, (I.Pi ((d_, Maybe), v_), s), occ ->
          checkClause
            ( gqr_,
              I.Decl (g_, N.decEName (g_, I.decSub (d_, s))),
              I.Decl (q_, C.Exist),
              (v_, I.dot1 s),
              P.body occ )
      | gqr_, g_, q_, (I.Pi (((I.Dec (_, v1_) as d_), No), v2_), s), occ ->
          checkClause
            ( gqr_,
              I.Decl (g_, I.decSub (d_, s)),
              I.Decl (q_, C.And (P.label occ)),
              (v2_, I.dot1 s),
              P.body occ )
      | ( ((g0_, q0_, rl_) as gqr_),
          g_,
          q_,
          ((I.Root (I.Const a, s_), s) as vs_),
          occ ) ->
          let n = I.ctxLength g_ in
          let rl'_ = C.shiftRCtx rl_ (function s -> I.comp (s, I.Shift n)) in
          checkSubgoals
            (concat (g0_, g_), concat (q0_, q_), rl'_, vs_, 0, (g_, q_))
      | gqr_, g_, q_, (I.Root (I.Def a, s_), s), occ ->
          raise
            (Error'
               ( occ,
                 (("Termination checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a))
                 ^ "." ))

    let rec checkClause' (vs_, occ) =
      checkClause ((I.Null, I.Null, []), I.Null, I.Null, vs_, occ)

    let rec checkRGoal (g_, q_, rl_, vs_, occ) =
      checkRGoalW (g_, q_, rl_, Whnf.whnf vs_, occ)

    and checkRGoalW = function
      | g_, q_, rl_, ((I.Root (I.Const a, s_), s) as vs_), occ -> ()
      | g_, q_, rl_, (I.Pi ((d_, Maybe), v_), s), occ ->
          checkRGoal
            ( I.Decl (g_, N.decLUName (g_, I.decSub (d_, s))),
              I.Decl (q_, C.All),
              C.shiftRCtx rl_ (function s -> I.comp (s, I.shift)),
              (v_, I.dot1 s),
              P.body occ )
      | g_, q_, rl_, (I.Pi (((I.Dec (_, v1_) as d_), No), v2_), s), occ -> begin
          checkRClause (g_, q_, rl_, (v1_, s), P.label occ);
          checkRGoal (g_, q_, rl_, (v2_, I.comp (I.invShift, s)), P.body occ)
        end
      | g_, q_, rl_, (I.Root (I.Def a, s_), s), occ ->
          raise
            (Error'
               ( occ,
                 (("Reduction checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a))
                 ^ "." ))

    and checkRImp (g_, q_, rl_, vs_, vs'_, occ) =
      checkRImpW (g_, q_, rl_, Whnf.whnf vs_, vs'_, occ)

    and checkRImpW = function
      | g_, q_, rl_, (I.Pi ((d'_, Maybe), v'_), s'), (v_, s), occ ->
          checkRImp
            ( I.Decl (g_, N.decEName (g_, I.decSub (d'_, s'))),
              I.Decl (q_, C.Exist),
              C.shiftRCtx rl_ (function s -> I.comp (s, I.shift)),
              (v'_, I.dot1 s'),
              (v_, I.comp (s, I.shift)),
              occ )
      | ( g_,
          q_,
          rl_,
          (I.Pi (((I.Dec (_, v1_) as d'_), No), v2_), s'),
          (v_, s),
          occ ) ->
          let rl'_ =
            begin match getROrder (g_, q_, (v1_, s'), occ) with
            | None -> rl_
            | Some o_ -> o_ :: rl_
            end
          in
          checkRImp (g_, q_, rl'_, (v2_, I.comp (I.invShift, s')), (v_, s), occ)
      | g_, q_, rl_, ((I.Root (I.Const a, s_), s) as vs'_), vs_, occ ->
          checkRGoal (g_, q_, rl_, vs_, occ)
      | g_, q_, rl_, ((I.Root (I.Def a, s_), s) as vs'_), vs_, occ ->
          raise
            (Error'
               ( occ,
                 (("Reduction checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a))
                 ^ "." ))

    and checkRClause (g_, q_, rl_, vs_, occ) =
      checkRClauseW (g_, q_, rl_, Whnf.whnf vs_, occ)

    and checkRClauseW = function
      | g_, q_, rl_, (I.Pi ((d_, Maybe), v_), s), occ ->
          checkRClause
            ( I.Decl (g_, N.decEName (g_, I.decSub (d_, s))),
              I.Decl (q_, C.Exist),
              C.shiftRCtx rl_ (function s -> I.comp (s, I.shift)),
              (v_, I.dot1 s),
              P.body occ )
      | g_, q_, rl_, (I.Pi (((I.Dec (_, v1_) as d_), No), v2_), s), occ ->
          let g'_ = I.Decl (g_, I.decSub (d_, s)) in
          let q'_ = I.Decl (q_, C.Exist) in
          let rl'_ = C.shiftRCtx rl_ (function s -> I.comp (s, I.shift)) in
          let rl''_ =
            begin match
              getROrder (g'_, q'_, (v1_, I.comp (s, I.shift)), occ)
            with
            | None -> rl'_
            | Some o_ -> o_ :: rl'_
            end
          in
          begin
            checkRClause (g'_, q'_, rl''_, (v2_, I.dot1 s), P.body occ);
            checkRImp
              ( g'_,
                q'_,
                rl''_,
                (v2_, I.dot1 s),
                (v1_, I.comp (s, I.shift)),
                P.label occ )
          end
      | g_, q_, rl_, ((I.Root (I.Const a, s_), s) as vs_), occ ->
          let ro_ =
            begin match selectROrder (a, (s_, s)) with
            | None ->
                raise
                  (Error'
                     ( occ,
                       ("No reduction order assigned for "
                       ^ N.qidToString (N.constQid a))
                       ^ "." ))
            | Some o_ -> o_
            end
          in
          let _ =
            begin if !Global.chatter > 4 then
              print
                (((("Verifying reduction property:\n" ^ rlistToString (g_, rl_))
                  ^ " ---> ")
                 ^ orderToString (g_, ro_))
                ^ " \n")
            else ()
            end
          in
          begin if C.deduce (g_, q_, rl_, ro_) then ()
          else
            raise
              (Error'
                 ( occ,
                   (("Reduction violation:\n" ^ rlistToString (g_, rl_))
                   ^ " ---> ")
                   ^ orderToString (g_, ro_) ))
          end
      | g_, q_, rl_, ((I.Root (I.Def a, s_), s) as vs_), occ ->
          raise
            (Error'
               ( occ,
                 (("Reduction checking for defined type families not yet \
                    available:\n" ^ "Illegal use of ")
                 ^ N.qidToString (N.constQid a))
                 ^ "." ))

    let rec checkFamReduction a =
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
      let _ =
        begin if !Global.chatter > 3 then
          print
            (("Reduction checking family " ^ N.qidToString (N.constQid a))
            ^ ":\n")
        else ()
        end
      in
      checkFam' (Index.lookup a)

    let rec checkFam a =
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
      let _ =
        begin if !Global.chatter > 3 then
          print
            (("Termination checking family " ^ N.qidToString (N.constQid a))
            ^ "\n")
        else ()
        end
      in
      checkFam' (Index.lookup a)

    let rec reset () =
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
