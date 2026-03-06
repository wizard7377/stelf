open! Basis;;
(* Meta printer for proof states *);;
(* Author: Carsten Schuermann *);;
module MetaPrint(MetaPrint__0: sig
                               module Global : GLOBAL
                               module MetaSyn' : METASYN
                               module Formatter : FORMATTER
                               module Print : PRINT
                               (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
                               module ClausePrint : CLAUSEPRINT
                               end) : METAPRINT
  =
  struct
    module MetaSyn = MetaSyn';;
    open!
      struct
        module M = MetaSyn;;
        module I = IntSyn;;
        module F = Formatter;;
        let rec modeToString = function 
                                        | top_ -> "+"
                                        | bot_ -> "-";;
        let rec depthToString b = begin if b <= 0 then "" else Int.toString b
          end;;
        let rec fmtPrefix gm_ =
          let rec fmtPrefix' =
            function 
                     | (M.Prefix (null_, null_, null_), fmt_) -> fmt_
                     | (M.Prefix
                        (I.Decl (null_, d_), I.Decl (null_, mode), I.Decl
                         (null_, b)),
                        fmt_)
                         -> [(F.String (depthToString b));
                             (F.String (modeToString mode));
                             Print.formatDec (I.null_, d_)] @ fmt_
                     | (M.Prefix
                        (I.Decl (g_, d_), I.Decl (m_, mode), I.Decl (b_, b)),
                        fmt_)
                         -> fmtPrefix'
                            ((M.Prefix (g_, m_, b_)),
                             [(F.String ","); F.space_; F.break_;
                              (F.String (depthToString b));
                              (F.String (modeToString mode));
                              Print.formatDec (g_, d_)] @ fmt_)
            in (F.HVbox (fmtPrefix' (gm_, [])));;
        let rec prefixToString gm_ = F.makestring_fmt (fmtPrefix gm_);;
        let rec stateToString
          (M.State (name, (M.Prefix (g_, m_, b_) as gm_), v_)) =
          ((((name ^ ":\n") ^ (prefixToString gm_)) ^ "\n--------------\n") ^
             (ClausePrint.clauseToString (g_, v_)))
            ^ "\n\n";;
        let rec sgnToString =
          function 
                   | sgnEmpty_ -> ""
                   | M.ConDec (e, s_)
                       -> (begin
                           if (! Global.chatter) >= 4 then
                           (Print.conDecToString e) ^ "\n" else begin
                           if (! Global.chatter) >= 3 then
                           (ClausePrint.conDecToString e) ^ "\n" else "" end
                           end) ^ (sgnToString s_);;
        end;;
    (* depthToString is used to format splitting depth *);;
    (* use explicitly quantified form *);;
    (* use form without quantifiers, which is reparsable *);;
    let modeToString = modeToString;;
    let sgnToString = sgnToString;;
    let stateToString = stateToString;;
    let conDecToString = ClausePrint.conDecToString;;
    end;;
(*! sharing ClausePrint.IntSyn = MetaSyn'.IntSyn !*);;
(* local *);;
(* functor MetaPrint *);;