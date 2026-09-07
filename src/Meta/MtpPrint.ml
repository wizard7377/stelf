open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Formatter.Formatter_
open! Print.Print_

(* # 1 "src/meta/Print.sig.ml" *)
open Funsyn
open Statesyn
open Funprint

(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)
include MTPPRINT
(* signature MTPRINT *)

(* # 1 "src/meta/Print.fun.ml" *)
open! Basis

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MTPrint (MTPrint__0 : sig
  (* Meta Printer Version 1.3 *)
  (* Author: Carsten Schuermann *)
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  module StateSyn' : STATESYN.STATESYN

  (*! sharing StateSyn'.FunSyn = FunSyn !*)
  (*! sharing StateSyn'.IntSyn = IntSyn !*)
  module Formatter' : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn !*)
  module FunPrint : FUNPRINT.FUNPRINT
end) : MTPPRINT.MTPRINT = struct
  open MTPrint__0
  module Formatter = Formatter'
  module StateSyn = StateSyn'

  exception Error = Error

  open! struct
    module I = IntSyn
    module N = Names
    module S = StateSyn
    module Fmt = Formatter
    module PrintFmt = Print.Formatter

    let printFmt f = Fmt.string (PrintFmt.makestring_fmt f)

    let nameState (S.State (n, (g, b), (ih, oh), d, o, h, f)) =
      ignore (Names.varReset I.Null);
      let g' = Names.ctxName g in
      S.State (n, (g', b), (ih, oh), d, o, h, f)

    let rec formatOrder (g, a) = match a with
      | S.Arg (us, vs) ->
          let u1, s1 = us in
          let u2, s2 = vs in
          [
            printFmt (Print.formatExp g (I.EClo (u1, s1)));
            Fmt.string ":";
            printFmt (Print.formatExp g (I.EClo (u2, s2)));
          ]
      | S.Lex os ->
          [
            Fmt.string "{";
            Fmt.hVbox0 1 0 1 (formatOrders (g, os));
            Fmt.string "}";
          ]
      | S.Simul os ->
          [
            Fmt.string "[";
            Fmt.hVbox0 1 0 1 (formatOrders (g, os));
            Fmt.string "]";
          ]

    and formatOrders (g, a) = match a with
      | [] -> []
      | o :: [] -> formatOrder (g, o)
      | o :: os ->
          formatOrder (g, o)
          @ [ Fmt.string ","; Fmt.break_ ]
          @ formatOrders (g, os)

    let formatTag (g, a) = match a with
      | S.Parameter l -> [ Fmt.string "<p>" ]
      | S.Lemma (S.Splits k) ->
          [ Fmt.string "<i"; Fmt.string (Int.toString k); Fmt.string ">" ]
      | S.Lemma S.Rl -> [ Fmt.string "<i >" ]
      | S.Lemma S.RLdone -> [ Fmt.string "<i*>" ]

    let rec formatCtx a1 b1 = match a1, b1 with
      | I.Null, b -> []
      | I.Decl (I.Null, d), I.Decl (I.Null, t) ->
          begin if !Global.chatter >= 4 then
            [
              Fmt.hVbox
                (formatTag (I.Null, t)
                @ [ Fmt.break_; printFmt (Print.formatDec I.Null d) ]);
            ]
          else [ printFmt (Print.formatDec I.Null d) ]
          end
      | I.Decl (g, d), I.Decl (b, t) ->
          begin if !Global.chatter >= 4 then
            formatCtx g b
            @ [ Fmt.string ","; Fmt.break_; Fmt.break_ ]
            @ [
                Fmt.hVbox
                  (formatTag (g, t)
                  @ [ Fmt.break_; printFmt (Print.formatDec g d) ]);
              ]
          else
            formatCtx g b
            @ [ Fmt.string ","; Fmt.break_ ]
            @ [ Fmt.break_; printFmt (Print.formatDec g d) ]
          end

    let formatState (S.State (n, (g, b), (ih, oh), d, o, h, f)) =
      Fmt.vbox0 0 1
        [
          Fmt.hVbox0 1 0 1 (formatOrder (g, o));
          Fmt.break_;
          Fmt.string "========================";
          Fmt.break_;
          Fmt.hVbox0 1 0 1 (formatCtx g b);
          Fmt.break_;
          Fmt.string "------------------------";
          Fmt.break_;
          Fmt.string
            (FunPrint.Formatter.makestring_fmt
               (FunPrint.formatForBare g f));
        ]

    let stateToString s = Fmt.makestring_fmt (formatState s)
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

(* # 1 "src/meta/MtpPrint.sml.ml" *)
