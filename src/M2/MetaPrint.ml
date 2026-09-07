open! Global.Global_
open! Intsyn.Lambda_
open! Formatter__Formatter_
open! Print
open! Print.Print_

(* # 1 "src/m2/MetaPrint.sig.ml" *)
open Metasyn

(* Meta printer for proof states *)
(* Author: Carsten Schuermann *)
include METAPRINT
(* signature METAPRINT.METAPRINT *)

(* # 1 "src/m2/MetaPrint.fun.ml" *)
open! Basis
open Metasyn
open ClausePrint

(* Meta printer for proof states *)
(* Author: Carsten Schuermann *)
module MetaPrint (MetaPrint__0 : sig
  module Global : GLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Formatter : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
  module ClausePrint : CLAUSEPRINT.CLAUSEPRINT
end) : METAPRINT with module MetaSyn = MetaPrint__0.MetaSyn' = struct
  open MetaPrint__0
  module MetaSyn = MetaSyn'

  open! struct
    module M = MetaSyn
    module I = IntSyn
    module F = Print.Formatter

    let modeToString = function M.Top -> "+" | M.Bot -> "-"

    let depthToString b =
      begin if b <= 0 then "" else Int.toString b
      end

    let fmtPrefix gm =
      let rec fmtPrefix' (a, fmt_) = match a with
        | M.Prefix (I.Null, I.Null, I.Null) -> fmt_
        | M.Prefix
              (I.Decl (I.Null, d_), I.Decl (I.Null, mode), I.Decl (I.Null, b)) ->
            [
              F.string (depthToString b);
              F.string (modeToString mode);
              Print.formatDec I.Null d_;
            ]
            @ fmt_
        | M.Prefix (I.Decl (g_, d_), I.Decl (m_, mode), I.Decl (b_, b)) ->
            fmtPrefix'
              ( M.Prefix (g_, m_, b_),
                [
                  F.string ",";
                  F.space;
                  F.break;
                  F.string (depthToString b);
                  F.string (modeToString mode);
                  Print.formatDec g_ d_;
                ]
                @ fmt_ )
      in
      F.hVbox (fmtPrefix' (gm, []))

    let prefixToString gm = F.makestring_fmt (fmtPrefix gm)

    let stateToString (M.State (name, (M.Prefix (g_, m_, b_) as gm), v_)) =
      ((((name ^ ":\n") ^ prefixToString gm) ^ "\n--------------\n")
      ^ ClausePrint.clauseToString g_ v_)
      ^ "\n\n"

    let rec sgnToString = function
      | sgnEmpty -> ""
      | M.ConDec (e, s_) ->
          begin if !Global.chatter >= 4 then Print.conDecToString e ^ "\n"
          else
            begin if !Global.chatter >= 3 then
              ClausePrint.conDecToString e ^ "\n"
            else ""
            end
          end
          ^ sgnToString s_
  end

  (* depthToString is used to format splitting depth *)
  (* use explicitly quantified form *)
  (* use form without quantifiers, which is reparsable *)
  let modeToString = modeToString
  let sgnToString = sgnToString
  let stateToString = stateToString
  let conDecToString = ClausePrint.conDecToString
end
(*! sharing ClausePrint.IntSyn = MetaSyn'.IntSyn !*)
(* local *)
(* functor MetaPrint *)

(* # 1 "src/m2/MetaPrint.sml.ml" *)
