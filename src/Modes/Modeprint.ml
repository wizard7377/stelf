open! Intsyn.Lambda_
open! Formatter.Formatter_
open! Print.Print_
open! Names.Names_

(* # 1 "src/modes/Modeprint.sig.ml" *)
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
      | I.Dec (_, v), M.Marg (_, (Some _ as name)) -> I.Dec (name, v)
      | d, M.Marg (_, None) -> d

    let makeSpine g =
      let rec makeSpine' (a, k, s) = match a with
        | I.Null -> s
        | I.Decl (g, _) ->
            makeSpine' (g, k + 1, I.App (I.Root (I.BVar k, I.Nil), s))
      in
      makeSpine' (g, 1, I.Nil)

    let fmtModeDec (cid, mS) =
      let v = I.constType cid in
      let rec fmtModeDec' (g, a, b) = match a, b with
        | _, M.Mnil ->
            [
              F.string "(";
              P.formatExp g (I.Root (I.Const cid, makeSpine g));
              F.string ")";
            ]
        | I.Pi ((d, _), v'), M.Mapp (marg, s) ->
            let d' = nameDec (d, marg) in
            let d'' = Names.decEName g d' in
            [
              F.string (argToString marg);
              F.string "{";
              P.formatDec g d'';
              F.string "}";
              F.break;
            ]
            @ fmtModeDec' (I.Decl (g, d''), v', s)
      in
      F.hVbox (fmtModeDec' (I.Null, v, mS))

    let rec fmtModeDecs = function
      | (cid, mS) :: [] -> [ fmtModeDec (cid, mS) ]
      | (cid, mS) :: mdecs ->
          fmtModeDec (cid, mS) :: F.break :: fmtModeDecs mdecs

    let modeToString cid mS = F.makestring_fmt (fmtModeDec (cid, mS))
    let modesToString mdecs = F.makestring_fmt (F.vbox0 0 1 (fmtModeDecs mdecs))
  end

  let modeToString = modeToString
  let modesToString = modesToString
end
(*! sharing Print.IntSyn = ModeSyn'.IntSyn !*)
(* local *)
(* functor ModePrint *)

(* # 1 "src/modes/Modeprint.sml.ml" *)
