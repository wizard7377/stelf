(* # 1 "src/meta/print.sig.ml" *)
open! Basis
open Funsyn
open Statesyn
open Funprint

(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)
module type MTPRINT = sig
  module Formatter : FORMATTER
  module StateSyn : STATESYN

  exception Error of string

  val nameState : StateSyn.state -> StateSyn.state
  val formatState : StateSyn.state -> Formatter.format
  val stateToString : StateSyn.state -> string
end
(* signature MTPRINT *)

(* # 1 "src/meta/print.fun.ml" *)
open! Global
open! Basis

module MTPrint (MTPrint__0 : sig
  (* Meta Printer Version 1.3 *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module StateSyn' : STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn !*)
  (*! sharing StateSyn'.IntSyn = IntSyn !*)
  module Formatter' : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module FunPrint : FUNPRINT
end) : MTPRINT = struct
  open MTPrint__0
  module Formatter = Formatter'
  module StateSyn = StateSyn'

  exception Error of string

  open! struct
    module I = IntSyn
    module N = Names
    module S = StateSyn
    module Fmt = Formatter
    module PrintFmt = Print.Formatter

    let printFmt f = Fmt.string (PrintFmt.makestring_fmt f)

    let rec nameState (S.State (n, (g_, b_), (ih_, oh_), d, o_, h_, f_)) =
      let _ = Names.varReset I.null_ in
      let g'_ = Names.ctxName g_ in
      S.State (n, (g'_, b_), (ih_, oh_), d, o_, h_, f_)

    let rec formatOrder = function
      | g_, S.Arg (us_, vs_) ->
          let u1_, s1_ = us_ in
          let u2_, s2_ = vs_ in
          [
            printFmt (Print.formatExp (g_, I.EClo (u1_, s1_)));
            Fmt.string ":";
            printFmt (Print.formatExp (g_, I.EClo (u2_, s2_)));
          ]
      | g_, S.Lex os_ ->
          [
            Fmt.string "{";
            Fmt.hVbox0 1 0 1 (formatOrders (g_, os_));
            Fmt.string "}";
          ]
      | g_, S.Simul os_ ->
          [
            Fmt.string "[";
            Fmt.hVbox0 1 0 1 (formatOrders (g_, os_));
            Fmt.string "]";
          ]

    and formatOrders = function
      | g_, [] -> []
      | g_, o_ :: [] -> formatOrder (g_, o_)
      | g_, o_ :: os_ ->
          formatOrder (g_, o_)
          @ [ Fmt.string ","; Fmt.break_ ]
          @ formatOrders (g_, os_)

    let rec formatTag = function
      | g_, S.Parameter l -> [ Fmt.string "<p>" ]
      | g_, S.Lemma (S.Splits k) ->
          [ Fmt.string "<i"; Fmt.string (Int.toString k); Fmt.string ">" ]
      | g_, S.Lemma S.Rl -> [ Fmt.string "<i >" ]
      | g_, S.Lemma S.RLdone -> [ Fmt.string "<i*>" ]

    let rec formatCtx = function
      | null_, b_ -> []
      | I.Decl (I.Null, d_), I.Decl (I.Null, t_) -> begin
          if !Global.chatter >= 4 then
            [
              Fmt.hVbox
                (formatTag (I.null_, t_)
                @ [ Fmt.break_; printFmt (Print.formatDec (I.null_, d_)) ]);
            ]
          else [ printFmt (Print.formatDec (I.null_, d_)) ]
        end
      | I.Decl (g_, d_), I.Decl (b_, t_) -> begin
          if !Global.chatter >= 4 then
            formatCtx (g_, b_)
            @ [ Fmt.string ","; Fmt.break_; Fmt.break_ ]
            @ [
                Fmt.hVbox
                  (formatTag (g_, t_)
                  @ [ Fmt.break_; printFmt (Print.formatDec (g_, d_)) ]);
              ]
          else
            formatCtx (g_, b_)
            @ [ Fmt.string ","; Fmt.break_ ]
            @ [ Fmt.break_; printFmt (Print.formatDec (g_, d_)) ]
        end

    let rec formatState (S.State (n, (g_, b_), (ih_, oh_), d, o_, h_, f_)) =
      Fmt.vbox0 0 1
        [
          Fmt.hVbox0 1 0 1 (formatOrder (g_, o_));
          Fmt.break_;
          Fmt.string "========================";
          Fmt.break_;
          Fmt.hVbox0 1 0 1 (formatCtx (g_, b_));
          Fmt.break_;
          Fmt.string "------------------------";
          Fmt.break_;
          Fmt.string
            (FunPrint.Formatter.makestring_fmt
               (FunPrint.formatForBare (g_, f_)));
        ]

    let rec stateToString s_ = Fmt.makestring_fmt (formatState s_)
  end

  (* nameState S = S'

       Invariant:
       If   |- S state     and S unnamed
       then |- S' State    and S' named
       and  |- S = S' state
    *)
  (* format T = fmt'

       Invariant:
       If   T is a tag
       then fmt' is a a format descibing the tag T
    *)
  (*      | formatTag (G, S.Assumption k) = [Fmt.String ""<a"",
                                         Fmt.String (Int.toString k),
                                         Fmt.String "">""] *)
  (* formatCtx (G, B) = fmt'

       Invariant:
       If   |- G ctx       and G is already named
       and  |- B : G tags
       then fmt' is a format describing the context (G, B)
    *)
  (* formatState S = fmt'

       Invariant:
       If   |- S state      and  S named
       then fmt' is a format describing the state S
    *)
  (* formatState S = S'

       Invariant:
       If   |- S state      and  S named
       then S' is a string descring state S in plain text
    *)
  let nameState = nameState
  let formatState = formatState
  let stateToString = stateToString
end
(*! sharing FunPrint.FunSyn = FunSyn !*)
(* local *)
(* functor MTPrint *)

(* # 1 "src/meta/mtp_print.sml.ml" *)
