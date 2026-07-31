open! Basis
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Intsyn
open! Intsyn.Lambda_
open! Formatter
open! Formatter__Formatter_
open! Print
open! Print.Print_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Index
open! Index.Index_

(* # 1 "src/modes/Modeprint.sig.ml" *)
open! Basis
open Modesyn

(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)
include MODEPRINT
(* signature MODEPRINT *)

(* # 1 "src/modes/Modeprint.fun.ml" *)
open! Basis

(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)
module MakeModePrint (Names : NAMES) (Formatter : FORMATTER) (Print : PRINT) :
  MODEPRINT = struct
  open! struct
    module I = IntSyn
    module M = ModeSyn
    module F = Print.Formatter
    module P = Print

    let modeToString = function
      | M.Plus -> "+"
      | M.Star -> "*"
      | M.Minus -> "-"
      | M.Minus1 -> "-1"

    let argToString (M.Marg (m, _)) = modeToString m

    let nameDec = function
      | I.Dec (_, v_), M.Marg (_, (Some _ as name)) -> I.Dec (name, v_)
      | d_, M.Marg (_, None) -> d_

    let makeSpine g_ =
      let rec makeSpine' = function
        | I.Null, _, s_ -> s_
        | I.Decl (g_, _), k, s_ ->
            makeSpine' (g_, k + 1, I.App (I.Root (I.BVar k, I.Nil), s_))
      in
      makeSpine' (g_, 1, I.Nil)

    let fmtModeDec (cid, mS) =
      let v_ = I.constType cid in
      let rec fmtModeDec' = function
        | g_, _, M.Mnil ->
            [
              F.string "(";
              P.formatExp (g_, I.Root (I.Const cid, makeSpine g_));
              F.string ")";
            ]
        | g_, I.Pi ((d_, _), v'_), M.Mapp (marg, s_) ->
            let d'_ = nameDec (d_, marg) in
            let d''_ = Names.decEName (g_, d'_) in
            [
              F.string (argToString marg);
              F.string "{";
              P.formatDec (g_, d''_);
              F.string "}";
              F.break;
            ]
            @ fmtModeDec' (I.Decl (g_, d''_), v'_, s_)
      in
      F.hVbox (fmtModeDec' (I.Null, v_, mS))

    let rec fmtModeDecs = function
      | (cid, mS) :: [] -> [ fmtModeDec (cid, mS) ]
      | (cid, mS) :: mdecs ->
          fmtModeDec (cid, mS) :: F.break :: fmtModeDecs mdecs

    let modeToString cM = F.makestring_fmt (fmtModeDec cM)
    let modesToString mdecs = F.makestring_fmt (F.vbox0 0 1 (fmtModeDecs mdecs))
  end

  let modeToString = modeToString
  let modesToString = modesToString
end
(*! sharing Print.IntSyn = ModeSyn'.IntSyn !*)
(* local *)
(* functor ModePrint *)

(* # 1 "src/modes/Modeprint.sml.ml" *)
