(* # 1 "src/meta/strategy.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open Mtp_global
open Mtp_filling
open Mtp_data
open Mtp_splitting
open Mtp_recursion
open Inference
open Mtp_print
open Timers
open Time_limit

(* MTPStrategy : Version 1.3 *)
(* Author: Carsten Schuermann *)
module type MTPSTRATEGY = sig
  module StateSyn : STATESYN

  val run : StateSyn.state list -> StateSyn.state list * StateSyn.state list
end

(* open cases -> remaining cases * solved cases *)
(* signature MTPSTRATEGY *)

(* # 1 "src/meta/strategy.fun.ml" *)
open! Global
open! Basis

(* MTP Strategy: Version 1.3 *)
(* Author: Carsten Schuermann *)
module MTPStrategy (MTPStrategy__0 : sig
  module MTPGlobal : MTPGLOBAL
  module StateSyn' : STATESYN
  module MTPFilling : MTPFILLING
  module MTPData : MTPDATA
  module MTPSplitting : MTPSPLITTING
  module MTPRecursion : MTPRECURSION
  module Inference : INFERENCE
  module MTPrint : MTPRINT
  module Timers : TIMERS
end) : MTPSTRATEGY = struct
  open MTPStrategy__0
  module StateSyn = StateSyn'

  open! struct
    module S = StateSyn

    let rec printInit () =
      begin if !Global.chatter > 3 then print "Strategy\n" else ()
      end

    let rec printFilling () =
      begin if !Global.chatter > 5 then print "[Filling ... "
      else begin
        if !Global.chatter > 4 then print "F" else ()
      end
      end

    let rec printRecursion () =
      begin if !Global.chatter > 5 then print "[Recursion ..."
      else begin
        if !Global.chatter > 4 then print "R" else ()
      end
      end

    let rec printInference () =
      begin if !Global.chatter > 5 then print "[Inference ..."
      else begin
        if !Global.chatter > 4 then print "I" else ()
      end
      end

    let rec printSplitting splitOp =
      begin if !Global.chatter > 5 then print "[Splitting ..."
      else begin
        if !Global.chatter > 4 then print "S" else ()
      end
      end

    let rec printCloseBracket () =
      begin if !Global.chatter > 5 then print "]\n" else ()
      end

    let rec printQed () =
      begin
        begin if !Global.chatter > 3 then print "[QED]\n" else ()
        end;
        begin if !Global.chatter > 4 then
          print
            (("Statistics: required Twelf.Prover.maxFill := "
             ^ Int.toString !MTPData.maxFill)
            ^ "\n")
        else ()
        end
      end

    let rec findMin = function
      | [] -> None
      | l_ ->
          let rec findMin' = function
            | [], result -> result
            | o'_ :: l'_, None -> begin
                if MTPSplitting.applicable o'_ then findMin' (l'_, Some o'_)
                else findMin' (l'_, None)
              end
            | o'_ :: l'_, Some o_ -> begin
                if MTPSplitting.applicable o'_ then begin
                  match MTPSplitting.compare (o'_, o_) with
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
          let _ = printSplitting splitOp in
          let sl_ = Timers.time Timers.splitting MTPSplitting.apply splitOp in
          let _ = printCloseBracket () in
          let _ = printRecursion () in
          let sl'_ =
            map
              (function
                | s_ ->
                    Timers.time Timers.recursion MTPRecursion.apply
                      (MTPRecursion.expand (Obj.magic s_)))
              sl_
          in
          let _ = printInference () in
          let sl''_ =
            map
              (function
                | s_ ->
                    Timers.time Timers.inference Inference.apply
                      (Inference.expand (Obj.magic s_)))
              sl'_
          in
          fill (Obj.magic sl''_ @ givenStates, os)
      end

    and fill = function
      | [], os -> os
      | s_ :: givenStates, ((openStates, solvedStates) as os) -> begin
          match
            Timers.time Timers.recursion MTPFilling.expand (Obj.magic s_)
          with
          | fillingOp -> (
              try
                let _ = printFilling () in
                let max, p_ =
                  TimeLimit.timeLimit !Global.timeLimit
                    (Timers.time Timers.filling MTPFilling.apply)
                    fillingOp
                in
                let _ = printCloseBracket () in
                fill (givenStates, os)
              with MTPFilling.Error _ -> split (s_ :: givenStates, os))
        end

    let rec run (givenStates : S.state list) =
      let _ = printInit () in
      let openStates, solvedStates = fill (Obj.magic givenStates, ([], [])) in
      let openStates' = map MTPrint.nameState (Obj.magic openStates) in
      let solvedStates' = map MTPrint.nameState (Obj.magic solvedStates) in
      let _ =
        begin match openStates with [] -> printQed () | _ -> ()
        end
      in
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

(* # 1 "src/meta/mtp_strategy.sml.ml" *)
