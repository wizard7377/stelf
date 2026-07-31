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

(* # 1 "src/meta/Prover.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open MtpGlobal
open MtpInit
open MtpStrategy
open Relfun

(* Meta Prover Version 1.3 *)
(* Author: Carsten Schuermann *)
include MTPPROVER
(* signature MTPROVER *)

(* # 1 "src/meta/Prover.fun.ml" *)
open! Basis

(* Meta Theorem Prover Version 1.3 *)
(* Author: Carsten Schuermann *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MTProver (MTProver__0 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL

  (*! structure IntSyn' : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn' !*)
  module StateSyn : STATESYN.STATESYN

  (*! sharing IntSyn = IntSyn' !*)
  (*! sharing StateSyn.FunSyn = FunSyn !*)
  module Order : ORDER

  (*! sharing Order.IntSyn = IntSyn' !*)
  module MTPInit : MTPINIT.MTPINIT

  (*! sharing MTPInit.FunSyn = FunSyn !*)
  module MTPStrategy : MTPSTRATEGY.MTPSTRATEGY
  module RelFun : RELFUN.RELFUN
end) : MTPPROVER.MTPROVER = struct
  open MTProver__0
  module StateSyn = StateSyn

  (*! structure IntSyn = IntSyn' !*)
  exception Error = Error

  open! struct
    module I = IntSyn
    module F = FunSyn
    module S = StateSyn

    let openStates : S.state list ref = ref []
    let solvedStates : S.state list ref = ref []

    let rec transformOrder' = function
      | g_, Order.Arg k ->
          let k' = I.ctxLength g_ - k + 1 in
          let (I.Dec (_, v_)) = I.ctxDec (g_, k') in
          S.Arg ((I.Root (I.BVar k', I.Nil), I.id), (v_, I.id))
      | g_, Order.Lex os_ ->
          S.Lex (map (function o_ -> transformOrder' (g_, o_)) os_)
      | g_, Order.Simul os_ ->
          S.Simul (map (function o_ -> transformOrder' (g_, o_)) os_)

    let rec transformOrder = function
      | g_, F.All (F.Prim d_, f_), os_ ->
          S.All (d_, transformOrder (I.Decl (g_, d_), f_, os_))
      | g_, F.And (f1_, f2_), o_ :: os_ ->
          S.And (transformOrder (g_, f1_, [ o_ ]), transformOrder (g_, f2_, os_))
      | g_, F.Ex _, o_ :: [] -> transformOrder' (g_, o_)
      | g_, true_, o_ :: [] -> transformOrder' (g_, o_)

    let select c = try Order.selLookup c with _ -> Order.Lex []
    let error s = raise (Error s)

    let reset () =
      begin
        openStates := [];
        solvedStates := []
      end

    let rec contains = function
      | [], _ -> true
      | x :: l_, l'_ ->
          List.exists (function x' -> x = x') l'_ && contains (l_, l'_)

    let equiv (l1_, l2_) = contains (l1_, l2_) && contains (l2_, l1_)
    let insertState s_ = openStates := s_ :: !openStates

    let rec cLToString = function
      | [] -> ""
      | c :: [] -> I.conDecName (I.sgnLookup c)
      | c :: l_ -> (I.conDecName (I.sgnLookup c) ^ ", ") ^ cLToString l_

    let init (k, (c :: _ as cL)) =
      ignore (MTPGlobal.maxFill := k);
      ignore (reset ());
      let cL' = try Order.closure c with Order.Error _ -> cL in
      let f_ = RelFun.convertFor cL in
      let o_ = transformOrder (I.Null, f_, map select cL) in
      begin if equiv (cL, cL') then
        List.app
          (function s_ -> insertState s_)
          (Obj.magic (MTPInit.init (f_, Obj.magic o_)))
      else
        raise
          (Error
             (("Theorem by simultaneous induction not correctly stated:"
             ^ "\n            expected: ")
             ^ cLToString cL'))
      end

    let auto () =
      let open_, solvedStates' = MTPStrategy.run (Obj.magic !openStates) in
      ignore (openStates := Obj.magic open_);
      ignore (solvedStates := !solvedStates @ Obj.magic solvedStates');
      begin if List.length !openStates > 0 then
        raise (Error "A proof could not be found")
      else ()
      end

    let print () = ()
    let install _ = ()
  end

  (* DISCLAIMER: This functor is temporary. Its purpose is to
       connect the new prover to Stelf  (see also functor below) *)
  (* List of open states *)
  (* List of solved states *)
  (* last case: no existentials---order must be trivial *)
  (* reset () = ()

       Invariant:
       Resets the internal state of open states/solved states
    *)
  (* contains (L1, L2) = B'

       Invariant:
       B' holds iff L1 subset of L2 (modulo permutation)
    *)
  (* equiv (L1, L2) = B'

       Invariant:
       B' holds iff L1 is equivalent to L2 (modulo permutation)
    *)
  (* insertState S = ()

       Invariant:
       If S is successful prove state, S is stored in solvedStates
       else S is stored in openStates
    *)
  (* cLtoString L = s

       Invariant:
       If   L is a list of cid,
       then s is a string, listing their names
    *)
  (* init (k, cL) = ()

       Invariant:
       If   k is the maximal search depth
       and  cL is a complete and consistent list of cids
       then init initializes the openStates/solvedStates
       else an Error exception is raised
    *)
  (* if no termination ordering given! *)
  (* auto () = ()

       Invariant:
       Solves as many States in openStates
       as possible.
    *)
  let init = init
  let auto = auto
  let print = print
  let install = install
end

(*! sharing RelFun.FunSyn = FunSyn !*)
(* local *)
(* functor MTProver *)
module CombiProver (CombiProver__1 : sig
  module MTPGlobal : MtpGlobal.MTPGLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module ProverOld : Prover.PROVER

  (*! sharing ProverOld.IntSyn = IntSyn' !*)
  module ProverNew : MTPPROVER.MTPROVER
end) : MTPPROVER.MTPROVER = struct
  open CombiProver__1

  (*! structure IntSyn = IntSyn' !*)
  exception Error = Error

  let he f =
    try f () with
    | ProverNew.Error s -> raise (Error s)
    | ProverOld.Error s -> raise (Error s)

  open! struct
    let init args_ =
      he (function () ->
          begin match !MTPGlobal.prover with
          | New -> ProverNew.init args_
          | Old -> ProverOld.init args_
          end)

    let auto args_ =
      he (function () ->
          begin match !MTPGlobal.prover with
          | New -> ProverNew.auto args_
          | Old -> ProverOld.auto args_
          end)

    let print args_ =
      he (function () ->
          begin match !MTPGlobal.prover with
          | New -> ProverNew.print args_
          | Old -> ProverOld.print args_
          end)

    let install args_ =
      he (function () ->
          begin match !MTPGlobal.prover with
          | New -> ProverNew.install args_
          | Old -> ProverOld.install args_
          end)
  end

  let init = init
  let auto = auto
  let print = print
  let install = install
end
(*! sharing ProverNew.IntSyn = IntSyn' !*)
(* functor CombiProver *)

(* # 1 "src/meta/MtpProver.sml.ml" *)
