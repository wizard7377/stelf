open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Timing

(* # 1 "src/m2/Prover.sig.ml" *)

(* Meta Prover *)
(* Author: Carsten Schuermann *)
include PROVER
(* signature PROVER *)

(* # 1 "src/m2/Prover.fun.ml" *)
open! Basis
open Metasyn
open MetaGlobal
open MetaPrint
open Timers

(* Meta Prover *)
(* Author: Carsten Schuermann *)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Prover (Prover__0 : sig
  module MetaGlobal : METAGLOBAL.METAGLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Init : INIT.INIT with module MetaSyn = MetaSyn'
  module Strategy : STRATEGY.STRATEGY with module MetaSyn = MetaSyn'
  module Filling : FILLING.FILLING with module MetaSyn = MetaSyn'
  module Splitting : SPLITTING.SPLITTING with module MetaSyn = MetaSyn'
  module Recursion : RECURSION.RECURSION with module MetaSyn = MetaSyn'
  module Qed : QED.QED with module MetaSyn = MetaSyn'
  module MetaPrint : METAPRINT.METAPRINT with module MetaSyn = MetaSyn'
  module Names : NAMES

  (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
  module Timers : TIMERS.TIMERS
end) : PROVER = struct
  open Prover__0

  (*! structure IntSyn = MetaSyn'.IntSyn !*)
  exception Error = Error

  open! struct
    module MetaSyn = MetaSyn'
    module M = MetaSyn
    module I = IntSyn

    let openStates : MetaSyn.state list ref = ref []
    let solvedStates : MetaSyn.state list ref = ref []
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

    let insertState s =
      begin if Qed.subgoal s then solvedStates := s :: !solvedStates
      else openStates := s :: !openStates
      end

    let rec cLToString = function
      | [] -> ""
      | c :: [] -> I.conDecName (I.sgnLookup c)
      | c :: l -> (I.conDecName (I.sgnLookup c) ^ ", ") ^ cLToString l

    let init k (c :: _ as cL) =
      ignore (MetaGlobal.maxFill := k);
      ignore (reset ());
      let cL' = try Order.closure c with Order.Error _ -> cL in
      begin if equiv cL cL' then
        List.app (function s -> insertState s) (Init.init cL)
      else
        raise
          (Error
             (("Theorem by simultaneous induction not correctly stated:"
             ^ "\n            expected: ")
             ^ cLToString cL'))
      end

    let auto () =
      ignore (print "M2.Prover.auto\n");
      let open', solvedStates' =
        try Strategy.run !openStates with
        | Splitting.Error s -> error ("Splitting Error: " ^ s)
        | Filling.Error s ->
            error ("A proof could not be found -- Filling Error: " ^ s)
        | Recursion.Error s -> error ("Recursion Error: " ^ s)
        | Filling.TimeOut ->
            error "A proof could not be found -- Exceeding Time Limit\n"
      in
      ignore (openStates := open');
      ignore (solvedStates := !solvedStates @ solvedStates');
      begin if List.length !openStates > 0 then
        raise (Error "A proof could not be found")
      else ()
      end

    let makeConDec (M.State (name, M.Prefix (g, m, b), v)) =
      let rec makeConDec' (a, v, k) = match a with
        | I.Null -> I.ConDec (name, None, k, I.Normal, v, I.Type)
        | I.Decl (g, d) ->
            makeConDec' (g, I.Pi ((d, I.Maybe), v), k + 1)
      in
      makeConDec' (g, v, 0)

    let rec makeSignature = function
      | [] -> M.SgnEmpty
      | s :: sl -> M.ConDec (makeConDec s, makeSignature sl)

    let install installConDec =
      let rec install' = function
        | M.SgnEmpty -> ()
        | M.ConDec (e, s) -> begin
            ignore (installConDec e);
            install' s
          end
      in
      let is =
        begin if List.length !openStates > 0 then
          raise (Error "Theorem not proven")
        else makeSignature !solvedStates
        end
      in
      install' is;
      begin if !Global.chatter > 2 then begin
        print "% ------------------\n";
        begin
          print (MetaPrint.sgnToString is);
          print "% ------------------\n"
        end
      end
      else ()
      end

    let printState () =
      let rec print' = function
        | [] -> ()
        | s :: l -> begin
            print (MetaPrint.stateToString s);
            print' l
          end
      in
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

(* # 1 "src/m2/Prover.sml.ml" *)
