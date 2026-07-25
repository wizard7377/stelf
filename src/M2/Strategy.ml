(* # 1 "src/m2/Strategy.sig.ml" *)
open! Basis
open Metasyn

(* Strategy *)
(* Author: Carsten Schuermann *)
include STRATEGY

(* open cases -> remaining cases * solved cases *)
(* signature STRATEGY *)

(* # 1 "src/m2/Strategy.fun.ml" *)
open! Splitting
open! Recursion
open! Lemma
open! Qed
open! Filling
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
      | o_ :: l_ ->
          let rec findMin' = function
            | [], k, result -> result
            | o'_ :: l'_, k, result ->
                let k' = Splitting.index o'_ in
                begin if Splitting.index o'_ < k then
                  findMin' (l'_, k', Some o'_)
                else findMin' (l'_, k, result)
                end
          in
          findMin' (l_, Splitting.index o_, Some o_)

    let rec split (s_ :: givenStates, ((openStates, solvedStates) as os)) =
      begin match
        findMin (Timers.time Timers.splitting Splitting.expand s_)
      with
      | None -> fill (givenStates, (s_ :: openStates, solvedStates))
      | Some splitOp -> (
          ignore (printSplitting ());
          let sl_ = Timers.time Timers.splitting Splitting.apply splitOp in
          ignore (printCloseBracket ());
          try fill (sl_ @ givenStates, os)
          with Splitting.Error _ ->
            fill (givenStates, (s_ :: openStates, solvedStates)))
      end

    and recurse (s_ :: givenStates, ((openStates, solvedStates) as os)) =
      begin match Timers.time Timers.recursion Recursion.expandEager s_ with
      | [] -> split (s_ :: givenStates, os)
      | recursionOp :: _ -> (
          ignore (printRecursion ());
          let s'_ = Timers.time Timers.recursion Recursion.apply recursionOp in
          ignore (printCloseBracket ());
          try fill (s'_ :: givenStates, (openStates, solvedStates))
          with Recursion.Error _ -> split (s_ :: givenStates, os))
      end

    and fill = function
      | [], os -> os
      | s_ :: givenStates, ((openStates, solvedStates) as os) -> (
          let fillOp () =
            begin match Timers.time Timers.filling Filling.expand s_ with
            | _, fillingOp -> (
                try
                  ignore (printFilling ());
                  let (s'_ :: []) =
                    Timers.time Timers.filling Filling.apply fillingOp
                  in
                  ignore (printCloseBracket ());
                  begin if Qed.subgoal s'_ then begin
                    printFinish s'_;
                    fill (givenStates, (openStates, s'_ :: solvedStates))
                  end
                  else fill (s'_ :: givenStates, os)
                  end
                with Filling.Error _ -> recurse (s_ :: givenStates, os))
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
      let _ =
        begin match os with [], _ -> printQed () | _ -> ()
        end
      in
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
      | o_ :: l_ ->
          let rec findMin' = function
            | [], k, result -> result
            | o'_ :: l'_, k, result ->
                let k' = Splitting.index o'_ in
                begin if Splitting.index o'_ < k then
                  findMin' (l'_, k', Some o'_)
                else findMin' (l'_, k, result)
                end
          in
          findMin' (l_, Splitting.index o_, Some o_)

    let rec split (s_ :: givenStates, ((openStates, solvedStates) as os)) =
      begin match
        findMin (Timers.time Timers.splitting Splitting.expand s_)
      with
      | None -> recurse (givenStates, (s_ :: openStates, solvedStates))
      | Some splitOp -> (
          ignore (printSplitting ());
          let sl_ = Timers.time Timers.splitting Splitting.apply splitOp in
          ignore (printCloseBracket ());
          try recurse (sl_ @ givenStates, os)
          with Splitting.Error _ ->
            recurse (givenStates, (s_ :: openStates, solvedStates)))
      end

    and fill = function
      | [], os -> os
      | s_ :: givenStates, ((openStates, solvedStates) as os) ->
          begin match Timers.time Timers.filling Filling.expand s_ with
          | _, fillingOp -> (
              try
                ignore (printFilling ());
                let (s'_ :: []) =
                  Timers.time Timers.filling Filling.apply fillingOp
                in
                ignore (printCloseBracket ());
                begin if Qed.subgoal s'_ then begin
                  printFinish s'_;
                  recurse (givenStates, (openStates, s'_ :: solvedStates))
                end
                else fill (s'_ :: givenStates, os)
                end
              with Filling.Error _ -> split (s_ :: givenStates, os))
          end

    and recurse = function
      | [], os -> os
      | s_ :: givenStates, ((openStates, solvedStates) as os) ->
          begin match Timers.time Timers.recursion Recursion.expandEager s_ with
          | [] -> fill (s_ :: givenStates, os)
          | recursionOp :: _ -> (
              ignore (printRecursion ());
              let s'_ =
                Timers.time Timers.recursion Recursion.apply recursionOp
              in
              ignore (printCloseBracket ());
              try recurse (s'_ :: givenStates, (openStates, solvedStates))
              with Recursion.Error _ -> fill (s_ :: givenStates, os))
          end

    let run givenStates =
      ignore (printInit ());
      let os = recurse (givenStates, ([], [])) in
      let _ =
        begin match os with [], _ -> printQed () | _ -> ()
        end
      in
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

  let run sl_ =
    begin match !MetaGlobal.strategy with
    | MetaGlobal.Rfs -> StrategyRFS.run sl_
    | MetaGlobal.Frs -> StrategyFRS.run sl_
    end
end
(* functor Strategy *)

(* # 1 "src/m2/Strategy.sml.ml" *)
