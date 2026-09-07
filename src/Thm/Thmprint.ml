open! Intsyn.Lambda_
open! Formatter.Formatter_

(* # 1 "src/thm/Thmprint.sig.ml" *)
open Thmsyn

(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)
include THMPRINT

(* -bp *)
(* signature THMPRINT *)

(* # 1 "src/thm/Thmprint.fun.ml" *)
open! Basis

(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
module ThmPrint (ThmPrint__0 : sig
  module ThmSyn' : THMSYN
  module Formatter : FORMATTER
end) : THMPRINT with module ThmSyn = ThmPrint__0.ThmSyn' = struct
  module ThmSyn = ThmPrint__0.ThmSyn'

  open! struct
    module L = ThmSyn
    module I = IntSyn
    module F = ThmPrint__0.Formatter

    let rec fmtIds = function
      | [] -> []
      | n :: [] -> [ F.string n ]
      | n :: l -> [ F.string n; F.string " " ] @ fmtIds l

    let rec fmtParams = function
      | [] -> []
      | Some n :: [] -> [ F.string n ]
      | None :: [] -> [ F.string "_" ]
      | Some n :: l -> [ F.string n; F.string " " ] @ fmtParams l
      | None :: l -> [ F.string "_"; F.string " " ] @ fmtParams l

    let fmtType (c, l) =
      F.hVbox
        ([ F.string (I.conDecName (I.sgnLookup c)); F.string " " ]
        @ fmtParams l)

    let rec fmtCallpats = function
      | [] -> []
      | t :: [] -> [ F.string "("; fmtType t; F.string ")" ]
      | t :: l -> [ F.string "("; fmtType t; F.string ") " ] @ fmtCallpats l

    let fmtOptions = function
      | _ :: [] as l -> [ F.hVbox (fmtIds l) ]
      | l -> [ F.string "("; F.hVbox (fmtIds l); F.string ") " ]

    let rec fmtOrder = function
      | L.Varg l ->
          begin match l with
          | h :: [] -> fmtIds l
          | _ -> [ F.string "("; F.hVbox (fmtIds l); F.string ")" ]
          end
      | L.Lex l -> [ F.string "{"; F.hVbox (fmtOrders l); F.string "}" ]
      | L.Simul l -> [ F.string "["; F.hVbox (fmtOrders l); F.string "]" ]

    and fmtOrders = function
      | [] -> []
      | o :: [] -> fmtOrder o
      | o :: l -> fmtOrder o @ (F.string " " :: fmtOrders l)

    let tDeclToString (L.TDecl (o, L.Callpats l)) =
      F.makestring_fmt
        (F.hVbox (fmtOrder o @ (F.string " " :: fmtCallpats l)))

    let callpatsToString (L.Callpats l) =
      F.makestring_fmt (F.hVbox (fmtCallpats l))

    let fmtROrder (L.RedOrder (p, o, o')) =
      begin match p with
      | Less -> fmtOrder o @ (F.string " < " :: fmtOrder o')
      | Leq -> fmtOrder o @ (F.string " <= " :: fmtOrder o')
      | Eq -> fmtOrder o @ (F.string " = " :: fmtOrder o')
      end

    let rOrderToString_ r = F.makestring_fmt (F.hVbox (fmtROrder r))

    let rDeclToString (L.RDecl (r, L.Callpats l)) =
      F.makestring_fmt
        (F.hVbox (fmtROrder r @ (F.string " " :: fmtCallpats l)))

    let tabledDeclToString (L.TabledDecl cid) =
      F.makestring_fmt (F.hVbox [ F.string (I.conDecName (I.sgnLookup cid)) ])

    let keepTableDeclToString (L.KeepTableDecl cid) =
      F.makestring_fmt (F.hVbox [ F.string (I.conDecName (I.sgnLookup cid)) ])
  end

  (* -bp *)
  let tDeclToString = tDeclToString
  let callpatsToString = callpatsToString
  let rOrderToString_ = rOrderToString_
  let rOrderToString = rOrderToString_

  (* -bp *)
  let rDeclToString = rDeclToString

  (* -bp *)
  let tabledDeclToString = tabledDeclToString
  let keepTableDeclToString = keepTableDeclToString
end
(* local *)
(* functor ThmPrint *)

(* # 1 "src/thm/Thmprint.sml.ml" *)
