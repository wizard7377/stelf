open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Subordinate
open! Subordinate
open! Modes
open! Modes.Modes_
open! Typecheck
open! Typecheck.Typecheck_
open! Index
open! Index.Index_
open! Opsem
open! Opsem.Opsem_
open! Compile
open! Compile.Compile_
open! Heuristic
open! Heuristic.Heuristic_
open! Timing
open! Timing.Timing_
open! Solvers
open! Solvers.Solvers_
open! M2
open! M2.M2_

(* # 1 "src/meta/Strategy.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open MtpGlobal
open MtpFilling
open MtpData
open MtpSplitting
open MtpRecursion
open Inference
open MtpPrint
open Timers
open TimeLimit

(* MTPStrategy : Version 1.3 *)
(* Author: Carsten Schuermann *)
include MTPSTRATEGY

(* open cases -> remaining cases * solved cases *)
(* signature MTPSTRATEGY *)

(* # 1 "src/meta/Strategy.fun.ml" *)
open! Global
open! Basis

(* MTP Strategy: Version 1.3 *)
(* Author: Carsten Schuermann *)
module MTPStrategy (MTPStrategy__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL
  module StateSyn' : STATESYN.STATESYN
  module MTPFilling : MTPFILLING.MTPFILLING
  module MTPData : MTPDATA.MTPDATA
  module MTPSplitting : MTPSPLITTING.MTPSPLITTING
  module MTPRecursion : MTPRECURSION.MTPRECURSION
  module Inference : INFERENCE.INFERENCE
  module MTPrint : MTPPRINT.MTPRINT
  module Timers : TIMERS.TIMERS
end) : MTPSTRATEGY = struct
  open MTPStrategy__0
  module StateSyn = StateSyn'

  open! struct
    module S = StateSyn

    let printInit () =
      begin if !Global.chatter > 3 then print "Strategy\n" else ()
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

    let printInference () =
      begin if !Global.chatter > 5 then print "[Inference ..."
      else
        begin if !Global.chatter > 4 then print "I" else ()
        end
      end

    let printSplitting splitOp =
      begin if !Global.chatter > 5 then print "[Splitting ..."
      else
        begin if !Global.chatter > 4 then print "S" else ()
        end
      end

    let printCloseBracket () =
      begin if !Global.chatter > 5 then print "]\n" else ()
      end

    let printQed () =
      begin
        begin if !Global.chatter > 3 then print "[QED]\n" else ()
        end;
        begin if !Global.chatter > 4 then
          print
            (("Statistics: required Stelf.Prover.maxFill := "
             ^ Int.toString !MTPData.maxFill)
            ^ "\n")
        else ()
        end
      end

    let findMin = function
      | [] -> None
      | l_ ->
          let rec findMin' = function
            | [], result -> result
            | o'_ :: l'_, None ->
                begin if MTPSplitting.applicable o'_ then
                  findMin' (l'_, Some o'_)
                else findMin' (l'_, None)
                end
            | o'_ :: l'_, Some o_ ->
                begin if MTPSplitting.applicable o'_ then
                  begin match MTPSplitting.compare o'_ o_ with
                  | Less -> findMin' (l'_, Some o'_)
                  | _ -> findMin' (l'_, Some o_)
                  end
                else findMin' (l'_, Some o_)
                end
          in
          findMin' (l_, None)

    let rec split (s_ :: givenStates, ((openStates, solvedStates) as os)) =
      begin match
        findMin (Timers.time Timers.splitting MTPSplitting.expand s_)
      with
      | None -> fill (givenStates, (s_ :: openStates, solvedStates))
      | Some splitOp ->
          ignore (printSplitting splitOp);
          let sl_ = Timers.time Timers.splitting MTPSplitting.apply splitOp in
          ignore (printCloseBracket ());
          ignore (printRecursion ());
          let sl' =
            map
              (function
                | s_ ->
                    Timers.time Timers.recursion MTPRecursion.apply
                      (MTPRecursion.expand (Obj.magic s_)))
              sl_
          in
          ignore (printInference ());
          let sl'' =
            map
              (function
                | s_ ->
                    Timers.time Timers.inference Inference.apply
                      (Inference.expand (Obj.magic s_)))
              sl'
          in
          fill (Obj.magic sl'' @ givenStates, os)
      end

    and fill = function
      | [], os -> os
      | s_ :: givenStates, ((openStates, solvedStates) as os) ->
          begin match
            Timers.time Timers.recursion MTPFilling.expand (Obj.magic s_)
          with
          | fillingOp -> (
              try
                ignore (printFilling ());
                let max, p_ =
                  TimeLimit.timeLimit !Global.timeLimit
                    (Timers.time Timers.filling MTPFilling.apply)
                    fillingOp
                in
                ignore (printCloseBracket ());
                fill (givenStates, os)
              with MTPFilling.Error _ -> split (s_ :: givenStates, os))
          end

    let run (givenStates : S.state list) =
      ignore (printInit ());
      let openStates, solvedStates = fill (Obj.magic givenStates, ([], [])) in
      let openStates' = map MTPrint.nameState (Obj.magic openStates) in
      let solvedStates' = map MTPrint.nameState (Obj.magic solvedStates) in
      ignore begin match openStates with [] -> printQed () | _ -> ()
        end;
      ( (Obj.magic openStates' : S.state list),
        (Obj.magic solvedStates' : S.state list) )
  end

  (* if !Global.chatter > 5 then print (""["" ^ MTPSplitting.menu splitOp) *)
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
  (* Note: calling splitting in case filling fails, may cause the prover to succeed
              if there are no cases to split -- however this may in fact be wrong -bp*)
  (* for comparing depth-first search (logic programming) with iterative deepening search
              in the meta-theorem prover, we must disallow splitting :

                handle TimeLimit.TimeOut =>  raise Filling.Error ""Time Out: Time limit exceeded\n""
                handle MTPFilling.Error msg =>  raise Filling.Error msg
                  ) handle MTPFilling.Error msg =>  raise Filling.Error msg
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

(* # 1 "src/meta/MtpStrategy.sml.ml" *)
