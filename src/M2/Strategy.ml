open! Global.Global_
open! Timing

(* # 1 "src/m2/Strategy.sig.ml" *)
open Metasyn

(* Strategy *)
(* Author: Carsten Schuermann *)
include STRATEGY

(* open cases -> remaining cases * solved cases *)
(* signature STRATEGY *)

(* # 1 "src/m2/Strategy.fun.ml" *)
open! Basis
open Metasyn
open MetaGlobal
open MetaPrint
open Timers
open TimeLimit

(* Strategy *)
(* Author: Carsten Schuermann *)
module StrategyFRS (StrategyFRS__0 : sig
  module MetaGlobal : METAGLOBAL.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Filling : FILLING.FILLING with module MetaSyn = MetaSyn'
  module Splitting : SPLITTING.SPLITTING with module MetaSyn = MetaSyn'
  module Recursion : RECURSION.RECURSION with module MetaSyn = MetaSyn'
  module Lemma : LEMMA.LEMMA with module MetaSyn = MetaSyn'
  module Qed : QED.QED with module MetaSyn = MetaSyn'
  module MetaPrint : METAPRINT.METAPRINT with module MetaSyn = MetaSyn'
  module Timers : TIMERS.TIMERS
end) : STRATEGY.STRATEGY with module MetaSyn = StrategyFRS__0.MetaSyn' = struct
  open StrategyFRS__0
  module MetaSyn = MetaSyn'

  open! struct
    module M = MetaSyn

    let printInit () =
      begin if !Global.chatter > 3 then print "Strategy 1.0: FRS\n" else ()
      end

    let printFinish (M.State (name, _, _)) =
      begin if !Global.chatter > 5 then print (("[Finished: " ^ name) ^ "]\n")
      else
        begin if !Global.chatter > 4 then print (("[" ^ name) ^ "]\n")
        else
          begin if !Global.chatter > 3 then print (("[" ^ name) ^ "]") else ()
          end
        end
      end

    let printFilling () =
      begin if !Global.chatter > 5 then print "[Filling ... "
      else
        begin if !Global.chatter > 4 then print "F" else ()
        end
      end

    let printRecursion () =
      begin if !Global.chatter > 5 then print "[Recursion ..."
      else
        begin if !Global.chatter > 4 then print "R" else ()
        end
      end

    let printSplitting () =
      begin if !Global.chatter > 5 then print "[Splitting ..."
      else
        begin if !Global.chatter > 4 then print "S" else ()
        end
      end

    let printCloseBracket () =
      begin if !Global.chatter > 5 then print "]\n" else ()
      end

    let printQed () =
      begin if !Global.chatter > 3 then print "[QED]\n" else ()
      end

    let findMin = function
      | [] -> None
      | o :: l ->
          let rec findMin' (a, k, result) = match a with
            | [] -> result
            | o' :: l' ->
                let k' = Splitting.index o' in
                begin if Splitting.index o' < k then
                  findMin' (l', k', Some o')
                else findMin' (l', k, result)
                end
          in
          findMin' (l, Splitting.index o, Some o)

    let rec split (s :: givenStates, ((openStates, solvedStates) as os)) =
      begin match
        findMin (Timers.time Timers.splitting Splitting.expand s)
      with
      | None -> fill (givenStates, (s :: openStates, solvedStates))
      | Some splitOp -> (
          ignore (printSplitting ());
          let sl = Timers.time Timers.splitting Splitting.apply splitOp in
          ignore (printCloseBracket ());
          try fill (sl @ givenStates, os)
          with Splitting.Error _ ->
            fill (givenStates, (s :: openStates, solvedStates)))
      end

    and recurse (s :: givenStates, ((openStates, solvedStates) as os)) =
      begin match Timers.time Timers.recursion Recursion.expandEager s with
      | [] -> split (s :: givenStates, os)
      | recursionOp :: _ -> (
          ignore (printRecursion ());
          let s' = Timers.time Timers.recursion Recursion.apply recursionOp in
          ignore (printCloseBracket ());
          try fill (s' :: givenStates, (openStates, solvedStates))
          with Recursion.Error _ -> split (s :: givenStates, os))
      end

    and fill = function
      | [], os -> os
      | s :: givenStates, ((openStates, solvedStates) as os) -> (
          let fillOp () =
            begin match Timers.time Timers.filling Filling.expand s with
            | _, fillingOp -> (
                try
                  ignore (printFilling ());
                  let (s' :: []) =
                    Timers.time Timers.filling Filling.apply fillingOp
                  in
                  ignore (printCloseBracket ());
                  begin if Qed.subgoal s' then begin
                    printFinish s';
                    fill (givenStates, (openStates, s' :: solvedStates))
                  end
                  else fill (s' :: givenStates, os)
                  end
                with Filling.Error _ -> recurse (s :: givenStates, os))
            end
          in
          try TimeLimit.timeLimit !Global.timeLimit fillOp ()
          with Filling.TimeOut ->
            begin
              print "\n----------- TIME OUT ---------------\n";
              raise Filling.TimeOut
            end)

    let run givenStates =
      ignore (printInit ());
      let os = fill (givenStates, ([], [])) in
      ignore begin match os with [], _ -> printQed () | _ -> ()
        end;
      os
  end

  (* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
  (* split   (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       recurse (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       fill    (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')

       Invariant:
       openStates' extends openStates and
         contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' extends solvedStates and
         contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
    *)
  (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
  let run = run
end

(* local *)
(* functor StrategyFRS *)
module StrategyRFS (StrategyRFS__1 : sig
  module MetaGlobal : METAGLOBAL.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Filling : FILLING.FILLING with module MetaSyn = MetaSyn'
  module Splitting : SPLITTING.SPLITTING with module MetaSyn = MetaSyn'
  module Recursion : RECURSION.RECURSION with module MetaSyn = MetaSyn'
  module Lemma : LEMMA.LEMMA with module MetaSyn = MetaSyn'
  module Qed : QED.QED with module MetaSyn = MetaSyn'
  module MetaPrint : METAPRINT.METAPRINT with module MetaSyn = MetaSyn'
  module Timers : TIMERS.TIMERS
end) : STRATEGY.STRATEGY with module MetaSyn = StrategyRFS__1.MetaSyn' = struct
  open StrategyRFS__1
  module MetaSyn = MetaSyn'

  open! struct
    module M = MetaSyn

    let printInit () =
      begin if !Global.chatter > 3 then print "Strategy 1.0: RFS\n" else ()
      end

    let printFinish (M.State (name, _, _)) =
      begin if !Global.chatter > 5 then print (("[Finished: " ^ name) ^ "]\n")
      else
        begin if !Global.chatter > 4 then print (("[" ^ name) ^ "]\n")
        else
          begin if !Global.chatter > 3 then print (("[" ^ name) ^ "]") else ()
          end
        end
      end

    let printFilling () =
      begin if !Global.chatter > 5 then print "[Filling ... "
      else
        begin if !Global.chatter > 4 then print "F" else ()
        end
      end

    let printRecursion () =
      begin if !Global.chatter > 5 then print "[Recursion ..."
      else
        begin if !Global.chatter > 4 then print "R" else ()
        end
      end

    let printSplitting () =
      begin if !Global.chatter > 5 then print "[Splitting ..."
      else
        begin if !Global.chatter > 4 then print "S" else ()
        end
      end

    let printCloseBracket () =
      begin if !Global.chatter > 5 then print "]\n" else ()
      end

    let printQed () =
      begin if !Global.chatter > 3 then print "[QED]\n" else ()
      end

    let findMin = function
      | [] -> None
      | o :: l ->
          let rec findMin' (a, k, result) = match a with
            | [] -> result
            | o' :: l' ->
                let k' = Splitting.index o' in
                begin if Splitting.index o' < k then
                  findMin' (l', k', Some o')
                else findMin' (l', k, result)
                end
          in
          findMin' (l, Splitting.index o, Some o)

    let rec split (s :: givenStates, ((openStates, solvedStates) as os)) =
      begin match
        findMin (Timers.time Timers.splitting Splitting.expand s)
      with
      | None -> recurse (givenStates, (s :: openStates, solvedStates))
      | Some splitOp -> (
          ignore (printSplitting ());
          let sl = Timers.time Timers.splitting Splitting.apply splitOp in
          ignore (printCloseBracket ());
          try recurse (sl @ givenStates, os)
          with Splitting.Error _ ->
            recurse (givenStates, (s :: openStates, solvedStates)))
      end

    and fill = function
      | [], os -> os
      | s :: givenStates, ((openStates, solvedStates) as os) ->
          begin match Timers.time Timers.filling Filling.expand s with
          | _, fillingOp -> (
              try
                ignore (printFilling ());
                let (s' :: []) =
                  Timers.time Timers.filling Filling.apply fillingOp
                in
                ignore (printCloseBracket ());
                begin if Qed.subgoal s' then begin
                  printFinish s';
                  recurse (givenStates, (openStates, s' :: solvedStates))
                end
                else fill (s' :: givenStates, os)
                end
              with Filling.Error _ -> split (s :: givenStates, os))
          end

    and recurse = function
      | [], os -> os
      | s :: givenStates, ((openStates, solvedStates) as os) ->
          begin match Timers.time Timers.recursion Recursion.expandEager s with
          | [] -> fill (s :: givenStates, os)
          | recursionOp :: _ -> (
              ignore (printRecursion ());
              let s' =
                Timers.time Timers.recursion Recursion.apply recursionOp
              in
              ignore (printCloseBracket ());
              try recurse (s' :: givenStates, (openStates, solvedStates))
              with Recursion.Error _ -> fill (s :: givenStates, os))
          end

    let run givenStates =
      ignore (printInit ());
      let os = recurse (givenStates, ([], [])) in
      ignore begin match os with [], _ -> printQed () | _ -> ()
        end;
      os
  end

  (* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
  (* split   (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       recurse (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       fill    (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')

       Invariant:
       openStates' extends openStates and
         contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' extends solvedStates and
         contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
    *)
  (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
  let run = run
end

(* local *)
(* functor StrategyRFS *)
module Strategy (Strategy__2 : sig
  module MetaGlobal : METAGLOBAL.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module StrategyFRS : STRATEGY.STRATEGY with module MetaSyn = MetaSyn'
  module StrategyRFS : STRATEGY.STRATEGY with module MetaSyn = MetaSyn'
end) : STRATEGY.STRATEGY with module MetaSyn = Strategy__2.MetaSyn' = struct
  open Strategy__2
  module MetaSyn = MetaSyn'

  let run sl =
    begin match !MetaGlobal.strategy with
    | MetaGlobal.Rfs -> StrategyRFS.run sl
    | MetaGlobal.Frs -> StrategyFRS.run sl
    end
end
(* functor Strategy *)

(* # 1 "src/m2/Strategy.sml.ml" *)
