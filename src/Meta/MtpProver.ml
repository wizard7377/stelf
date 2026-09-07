open! Intsyn.Lambda_
open! M2

(* # 1 "src/meta/Prover.sig.ml" *)
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

    let rec transformOrder' (g, a) = match a with
      | Order.Arg k ->
          let k' = I.ctxLength g - k + 1 in
          let (I.Dec (_, v)) = I.ctxDec g k' in
          S.Arg ((I.Root (I.BVar k', I.Nil), I.id), (v, I.id))
      | Order.Lex os ->
          S.Lex (map (function o -> transformOrder' (g, o)) os)
      | Order.Simul os ->
          S.Simul (map (function o -> transformOrder' (g, o)) os)

    let rec transformOrder (g, true_, a) = match true_, a with
      | F.All (F.Prim d, f), os ->
          S.All (d, transformOrder (I.Decl (g, d), f, os))
      | F.And (f1, f2), o :: os ->
          S.And (transformOrder (g, f1, [ o ]), transformOrder (g, f2, os))
      | F.Ex _, o :: [] -> transformOrder' (g, o)
      | true_, o :: [] -> transformOrder' (g, o)

    let select c = try Order.selLookup c with _ -> Order.Lex []
    let error s = raise (Error s)

    let reset () =
      begin
        openStates := [];
        solvedStates := []
      end

    let rec contains (a, l') = match a with
      | [] -> true
      | x :: l ->
          List.exists (function x' -> x = x') l' && contains (l, l')

    let equiv l1 l2 = contains (l1, l2) && contains (l2, l1)
    let insertState s = openStates := s :: !openStates

    let rec cLToString = function
      | [] -> ""
      | c :: [] -> I.conDecName (I.sgnLookup c)
      | c :: l -> (I.conDecName (I.sgnLookup c) ^ ", ") ^ cLToString l

    let init k (c :: _ as cL) =
      ignore (MTPGlobal.maxFill := k);
      ignore (reset ());
      let cL' = try Order.closure c with Order.Error _ -> cL in
      let f = RelFun.convertFor cL in
      let o = transformOrder (I.Null, f, map select cL) in
      begin if equiv cL cL' then
        List.app
          (function s -> insertState s)
          (Obj.magic (MTPInit.init f (Obj.magic o)))
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
    let init args =
      he (function () ->
          begin match !MTPGlobal.prover with
          | New -> ProverNew.init args
          | Old -> ProverOld.init args
          end)

    let auto args =
      he (function () ->
          begin match !MTPGlobal.prover with
          | New -> ProverNew.auto args
          | Old -> ProverOld.auto args
          end)

    let print args =
      he (function () ->
          begin match !MTPGlobal.prover with
          | New -> ProverNew.print args
          | Old -> ProverOld.print args
          end)

    let install args =
      he (function () ->
          begin match !MTPGlobal.prover with
          | New -> ProverNew.install args
          | Old -> ProverOld.install args
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
