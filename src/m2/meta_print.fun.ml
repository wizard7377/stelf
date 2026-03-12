open! Basis
open Metasyn
open Clause_print

(* Meta printer for proof states *)
(* Author: Carsten Schuermann *)
module MetaPrint (MetaPrint__0 : sig
  module Global : GLOBAL
  module MetaSyn' : METASYN
  module Formatter : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
  module ClausePrint : CLAUSEPRINT
end) : METAPRINT with module MetaSyn = MetaPrint__0.MetaSyn' = struct
  open MetaPrint__0
  module MetaSyn = MetaSyn'

  open! struct
    module M = MetaSyn
    module I = IntSyn
    module F = Print.Formatter

    let rec modeToString = function top_ -> "+" | bot_ -> "-"

    let rec depthToString b =
      begin if b <= 0 then "" else Int.toString b
      end

    let rec fmtPrefix gm_ =
      let rec fmtPrefix' = function
        | M.Prefix (Null, Null, Null), fmt_ -> fmt_
        | ( M.Prefix (I.Decl (Null, d_), I.Decl (Null, mode), I.Decl (Null, b)),
            fmt_ ) ->
            [
              F.string (depthToString b);
              F.string (modeToString mode);
              Print.formatDec (I.Null, d_);
            ]
            @ fmt_
        | M.Prefix (I.Decl (g_, d_), I.Decl (m_, mode), I.Decl (b_, b)), fmt_ ->
            fmtPrefix'
              ( M.Prefix (g_, m_, b_),
                [
                  F.string ",";
                  F.space;
                  F.break;
                  F.string (depthToString b);
                  F.string (modeToString mode);
                  Print.formatDec (g_, d_);
                ]
                @ fmt_ )
      in
      F.hVbox (fmtPrefix' (gm_, []))

    let rec prefixToString gm_ = F.makestring_fmt (fmtPrefix gm_)

    let rec stateToString (M.State (name, (M.Prefix (g_, m_, b_) as gm_), v_)) =
      ((((name ^ ":\n") ^ prefixToString gm_) ^ "\n--------------\n")
      ^ ClausePrint.clauseToString (g_, v_))
      ^ "\n\n"

    let rec sgnToString = function
      | sgnEmpty_ -> ""
      | M.ConDec (e, s_) ->
          begin if !Global.chatter >= 4 then Print.conDecToString e ^ "\n"
          else begin
            if !Global.chatter >= 3 then ClausePrint.conDecToString e ^ "\n"
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
