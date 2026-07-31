open! Basis
open! Stream
open! Stream.Stream_
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Modes
open! Modes.Modes_
open! Paths
open! Paths.Paths_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Terminate
open! Terminate.Terminate_
open! Index
open! Index.Index_
open! Thm
open! Thm.Thm_
open! Opsem
open! Opsem.Opsem_
open! Compile
open! Compile.Compile_
open! Subordinate
open! Subordinate
open! Table
open! Table.Table_
open! Timing
open! Timing.Timing_
open! Solvers
open! Solvers.Solvers_

(* # 1 "src/m2/Skolem.sig.ml" *)
open! Basis

(* Skolem administration *)
(* Author: Carsten Schuermann *)
include SKOLEM
(* signature SKOLEM *)

(* # 1 "src/m2/Skolem.fun.ml" *)
open! Basis
open Metasyn
open Modetable
open Timers

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Skolem (Skolem__0 : sig
  (* Skolem constant administration *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module IndexSkolem : INDEX

  (*! sharing IndexSkolem.IntSyn = IntSyn' !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing Modes.Modesyn.ModeSyn.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Compile : COMPILE

  (*! sharing Compile.IntSyn = IntSyn' !*)
  module Timers : TIMERS.TIMERS
  module Names : NAMES
end) : SKOLEM = struct
  open Skolem__0

  (*! structure IntSyn = IntSyn' !*)
  exception Error = Error

  open! struct
    module I = IntSyn
    module M = Modes.Modesyn.ModeSyn

    let installSkolem (name, imp, (v_, mS), l_) =
      let rec spine = function
        | 0 -> I.Nil
        | n -> I.App (I.Root (I.BVar n, I.Nil), spine (n - 1))
      in
      let rec installSkolem' = function
        | d, (I.Pi ((d_, dp_), v_), mS), s, k ->
            begin match mS with
            | M.Mapp (M.Marg (M.Plus, _), mS') ->
                installSkolem'
                  ( d + 1,
                    (v_, mS'),
                    I.dot1 s,
                    function
                    | v_ ->
                        k
                          (Abstract.piDepend
                             ((Whnf.normalizeDec (d_, s), I.Meta), v_)) )
            | M.Mapp (M.Marg (M.Minus, _), mS') ->
                let (I.Dec (_, v'_)) = d_ in
                let v'' = k (Whnf.normalize (v'_, s)) in
                let name' = Names.skonstName (name ^ "#") in
                let sd_ = I.SkoDec (name', None, imp, v'', l_) in
                let sk = I.sgnAdd sd_ in
                let h_ = I.Skonst sk in
                ignore (IndexSkolem.install I.Ordinary h_);
                ignore (Names.installConstName sk);
                let _ =
                  Timers.time Timers.compiling Compile.install I.Ordinary sk
                in
                let s_ = spine d in
                ignore (Display.chatter_s 3 (Print.conDecToString sd_ ^ "\n"));
                installSkolem'
                  (d, (v_, mS'), I.Dot (I.Exp (I.Root (h_, s_)), s), k)
            end
        | _, (I.Uni _, M.Mnil), _, _ -> ()
      in
      installSkolem' (0, (v_, mS), I.id, function v_ -> v_)

    let rec install = function
      | [] -> ()
      | a :: aL ->
          let (I.ConDec (name, _, imp, _, v_, l_)) = I.sgnLookup a in
          let (Some mS) = ModeTable.modeLookup a in
          ignore (installSkolem (name, imp, (v_, mS), I.Type));
          install aL
  end

  (*! structure CompSyn = Compile.CompSyn !*)
  (* installSkolem (name, k, (V, mS), L) =

       Invariant:
            name is the name of a theorem
       and  imp is the number of implicit arguments
       and  V is its term together with the mode assignment mS
       and  L is the level of the declaration

       Effects: New Skolem constants are generated, named, and indexed
    *)
  (* spine n = S'

           Invariant:
           S' = n; n-1; ... 1; Nil
        *)
  (* installSkolem' ((V, mS), s, k) = ()

           Invariant:
                G |- V : type
           and  G' |- s : G
           and  |G'| = d
           and  k is a continuation, mapping a type G' |- V' type
                to . |- {{G'}} V'

           Effects: New Skolem constants are generated, named, and indexed
        *)
  (*                                  fn V => k (I.Pi ((Whnf.normalizeDec (D, s), DP), V))) *)
  (*                  val CompSyn.SClause r = CompSyn.sProgLookup sk *)
  (* install L = ()

       Invariant:
           L is a list of a's (mututal inductive theorems)
           which have an associated mode declaration

       Effect: Skolem constants for all theorems are generated, named, and indexed
    *)
  let install = install
end
(*! sharing Names.IntSyn = IntSyn' !*)
(* local *)
(* functor Skolem *)

(* # 1 "src/m2/Skolem.sml.ml" *)
