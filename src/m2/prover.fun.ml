open! Strategy
open! Filling
open! Splitting
open! Recursion
open! Qed
open! Init
open! Basis
open Metasyn
open Meta_global
open Meta_print
open Timers

(* Meta Prover *)
(* Author: Carsten Schuermann *)
module Prover (Prover__0 : sig
  module MetaGlobal : METAGLOBAL
  module MetaSyn' : METASYN
  module Init : INIT with module MetaSyn = MetaSyn'
  module Strategy : STRATEGY with module MetaSyn = MetaSyn'
  module Filling : FILLING with module MetaSyn = MetaSyn'
  module Splitting : SPLITTING with module MetaSyn = MetaSyn'
  module Recursion : RECURSION with module MetaSyn = MetaSyn'
  module Qed : QED with module MetaSyn = MetaSyn'
  module MetaPrint : METAPRINT with module MetaSyn = MetaSyn'
  module Names : NAMES

  (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
  module Timers : TIMERS
end) : PROVER = struct
  open Prover__0
  (*! structure IntSyn = MetaSyn'.IntSyn !*)
  exception Error of string

  open! struct
    module MetaSyn = MetaSyn'
    module M = MetaSyn
    module I = IntSyn

    let openStates : MetaSyn.state_ list ref = ref []
    let solvedStates : MetaSyn.state_ list ref = ref []
    let rec error s = raise (Error s)

    let rec reset () =
      begin
        openStates := [];
        solvedStates := []
      end

    let rec contains = function
      | [], _ -> true
      | x :: l_, l'_ ->
          List.exists (function x' -> x = x') l'_ && contains (l_, l'_)

    let rec equiv (l1_, l2_) = contains (l1_, l2_) && contains (l2_, l1_)

    let rec insertState s_ =
      begin if Qed.subgoal s_ then solvedStates := s_ :: !solvedStates
      else openStates := s_ :: !openStates
      end

    let rec cLToString = function
      | [] -> ""
      | c :: [] -> I.conDecName (I.sgnLookup c)
      | c :: l_ -> (I.conDecName (I.sgnLookup c) ^ ", ") ^ cLToString l_

    let rec init (k, (c :: _ as cL)) =
      let _ = MetaGlobal.maxFill := k in
      let _ = reset () in
      let cL' = try Order.closure c with Order.Error _ -> cL in
      begin if equiv (cL, cL') then
        List.app (function s_ -> insertState s_) (Init.init cL)
      else
        raise
          (Error
             (("Theorem by simultaneous induction not correctly stated:"
             ^ "\n            expected: ")
             ^ cLToString cL'))
      end

    let rec auto () =
      let _ = print "M2.Prover.auto\n" in
      let open', solvedStates' =
        try Strategy.run !openStates with
        | Splitting.Error s -> error ("Splitting Error: " ^ s)
        | Filling.Error s ->
            error ("A proof could not be found -- Filling Error: " ^ s)
        | Recursion.Error s -> error ("Recursion Error: " ^ s)
        | timeOut_ ->
            error "A proof could not be found -- Exceeding Time Limit\n"
      in
      let _ = openStates := open' in
      let _ = solvedStates := !solvedStates @ solvedStates' in
      begin if List.length !openStates > 0 then
        raise (Error "A proof could not be found")
      else ()
      end

    let rec makeConDec (M.State (name, M.Prefix (g_, m_, b_), v_)) =
      let rec makeConDec' = function
        | I.Null, v_, k -> I.ConDec (name, None, k, I.Normal, v_, I.Type)
        | I.Decl (g_, d_), v_, k ->
            makeConDec' (g_, I.Pi ((d_, I.Maybe), v_), k + 1)
      in
      makeConDec' (g_, v_, 0)

    let rec makeSignature = function
      | [] -> M.SgnEmpty
      | s_ :: sl_ -> M.ConDec (makeConDec s_, makeSignature sl_)

    let rec install installConDec =
      let rec install' = function
        | M.SgnEmpty -> ()
        | M.ConDec (e, s_) -> begin
            let _ = installConDec e in
            install' s_
          end
      in
      let is_ =
        begin if List.length !openStates > 0 then
          raise (Error "Theorem not proven")
        else makeSignature !solvedStates
        end
      in
      begin
        install' is_;
        begin if !Global.chatter > 2 then begin
          print "% ------------------\n";
          begin
            print (MetaPrint.sgnToString is_);
            print "% ------------------\n"
          end
        end
        else ()
        end
      end

    let rec printState () =
      let rec print' = function
        | [] -> ()
        | s_ :: l_ -> begin
            print (MetaPrint.stateToString s_);
            print' l_
          end
      in
      begin
        print "Open problems:\n";
        begin
          print "==============\n\n";
          begin
            print' !openStates;
            begin
              print "Solved problems:\n";
              begin
                print "================\n\n";
                print' !solvedStates
              end
            end
          end
        end
      end
  end

  (* List of open states *)
  (* List of solved states *)
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
  (* makeConDec (name, (G, M), V) = e'

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  G |- V : type
       then e' = (name, |G|, {G}.V, Type) is a signature conDec
    *)
  (* makeSignature (SL) = IS'

       Invariant:
       If   SL is a list of states,
       then IS' is the corresponding interface signaure
    *)
  (* install () = ()

       Invariant:
       Installs solved states into the global signature.
    *)
  (* print () = ()

       Invariant:
       Prints the list of open States and the list of closed states.
    *)
  let print = printState
  let init = init
  let auto = auto
  let install = install
end
(* local *)
(* functor Prover *)
