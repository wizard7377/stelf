(* # 1 "src/thm/thmprint.sig.ml" *)
open! Basis
open Thmsyn

(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)
include Thmprint_intf
(* -bp *)
(* signature THMPRINT *)

(* # 1 "src/thm/thmprint.fun.ml" *)
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
      | n :: l_ -> [ F.string n; F.string " " ] @ fmtIds l_

    let rec fmtParams = function
      | [] -> []
      | Some n :: [] -> [ F.string n ]
      | None :: [] -> [ F.string "_" ]
      | Some n :: l_ -> [ F.string n; F.string " " ] @ fmtParams l_
      | None :: l_ -> [ F.string "_"; F.string " " ] @ fmtParams l_

    let rec fmtType (c, l_) =
      F.hVbox
        ([ F.string (I.conDecName (I.sgnLookup c)); F.string " " ]
        @ fmtParams l_)

    let rec fmtCallpats = function
      | [] -> []
      | t_ :: [] -> [ F.string "("; fmtType t_; F.string ")" ]
      | t_ :: l_ -> [ F.string "("; fmtType t_; F.string ") " ] @ fmtCallpats l_

    let rec fmtOptions = function
      | _ :: [] as l_ -> [ F.hVbox (fmtIds l_) ]
      | l_ -> [ F.string "("; F.hVbox (fmtIds l_); F.string ") " ]

    let rec fmtOrder = function
      | L.Varg l_ -> begin
          match l_ with
          | h_ :: [] -> fmtIds l_
          | _ -> [ F.string "("; F.hVbox (fmtIds l_); F.string ")" ]
        end
      | L.Lex l_ -> [ F.string "{"; F.hVbox (fmtOrders l_); F.string "}" ]
      | L.Simul l_ -> [ F.string "["; F.hVbox (fmtOrders l_); F.string "]" ]

    and fmtOrders = function
      | [] -> []
      | o_ :: [] -> fmtOrder o_
      | o_ :: l_ -> fmtOrder o_ @ (F.string " " :: fmtOrders l_)

    let rec tDeclToString (L.TDecl (o_, L.Callpats l_)) =
      F.makestring_fmt
        (F.hVbox (fmtOrder o_ @ (F.string " " :: fmtCallpats l_)))

    let rec callpatsToString (L.Callpats l_) =
      F.makestring_fmt (F.hVbox (fmtCallpats l_))

    let rec fmtROrder (L.RedOrder (p_, o_, o'_)) =
      begin match p_ with
      | Less -> fmtOrder o_ @ (F.string " < " :: fmtOrder o'_)
      | Leq -> fmtOrder o_ @ (F.string " <= " :: fmtOrder o'_)
      | Eq -> fmtOrder o_ @ (F.string " = " :: fmtOrder o'_)
      end

    let rec rOrderToString_ r_ = F.makestring_fmt (F.hVbox (fmtROrder r_))

    let rec rDeclToString (L.RDecl (r_, L.Callpats l_)) =
      F.makestring_fmt
        (F.hVbox (fmtROrder r_ @ (F.string " " :: fmtCallpats l_)))

    let rec tabledDeclToString (L.TabledDecl cid) =
      F.makestring_fmt (F.hVbox [ F.string (I.conDecName (I.sgnLookup cid)) ])

    let rec keepTableDeclToString (L.KeepTableDecl cid) =
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

(* # 1 "src/thm/thmprint.sml.ml" *)
