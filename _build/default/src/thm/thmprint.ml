# 1 "src/thm/thmprint.sig.ml"
open! Basis;;
(* Printer for Meta Theorems *);;
(* Author: Carsten Schuermann *);;
module type THMPRINT = sig
                       module ThmSyn : THMSYN
                       val tDeclToString : ThmSyn.tDecl_ -> string
                       val callpatsToString : ThmSyn.callpats_ -> string
                       val rDeclToString : ThmSyn.rDecl_ -> string
                       (* -bp *)
                       val rOrderToString : ThmSyn.redOrder_ -> string
                       (* -bp *)
                       val tabledDeclToString : ThmSyn.tabledDecl_ -> string
                       (* -bp *)
                       val
                         keepTableDeclToString : ThmSyn.keepTableDecl_ ->
                                                 string
                       end;;
(* -bp *);;
(* signature THMPRINT *);;
# 1 "src/thm/thmprint.fun.ml"
open! Basis;;
(* Printer for Meta Theorems *);;
(* Author: Carsten Schuermann *);;
(* Modified: Brigitte Pientka *);;
module ThmPrint(ThmPrint__0: sig
                             module ThmSyn' : THMSYN
                             module Formatter : FORMATTER
                             end) : THMPRINT
  =
  struct
    module ThmSyn = ThmSyn';;
    open!
      struct
        module L = ThmSyn;;
        module I = IntSyn;;
        module F = Formatter;;
        let rec fmtIds =
          function 
                   | [] -> []
                   | (n :: []) -> [(F.String n)]
                   | (n :: l_)
                       -> [(F.String n); (F.String " ")] @ (fmtIds l_);;
        let rec fmtParams =
          function 
                   | [] -> []
                   | (Some n :: []) -> [(F.String n)]
                   | (None :: []) -> [(F.String "_")]
                   | (Some n :: l_)
                       -> [(F.String n); (F.String " ")] @ (fmtParams l_)
                   | (None :: l_)
                       -> [(F.String "_"); (F.String " ")] @ (fmtParams l_);;
        let rec fmtType (c, l_) =
          (F.HVbox
           ([(F.String (I.conDecName (I.sgnLookup c))); (F.String " ")] @
              (fmtParams l_)));;
        let rec fmtCallpats =
          function 
                   | [] -> []
                   | (T :: []) -> [(F.String "("); fmtType T; (F.String ")")]
                   | (T :: l_)
                       -> [(F.String "("); fmtType T; (F.String ") ")] @
                            (fmtCallpats l_);;
        let rec fmtOptions =
          function 
                   | ((_ :: []) as l_) -> [(F.HVbox (fmtIds l_))]
                   | l_
                       -> [(F.String "("); (F.HVbox (fmtIds l_));
                           (F.String ") ")];;
        let rec fmtOrder =
          function 
                   | L.Varg l_
                       -> begin
                          match l_
                          with 
                               | (h_ :: []) -> fmtIds l_
                               | _
                                   -> [(F.String "("); (F.HVbox (fmtIds l_));
                                       (F.String ")")]
                          end
                   | L.Lex l_
                       -> [(F.String "{"); (F.HVbox (fmtOrders l_));
                           (F.String "}")]
                   | L.Simul l_
                       -> [(F.String "["); (F.HVbox (fmtOrders l_));
                           (F.String "]")]
        and fmtOrders =
          function 
                   | [] -> []
                   | (o_ :: []) -> fmtOrder o_
                   | (o_ :: l_)
                       -> (fmtOrder o_) @ (((F.String " ") :: fmtOrders l_));;
        let rec tDeclToString (L.TDecl (o_, L.Callpats l_)) =
          F.makestring_fmt
          ((F.HVbox ((fmtOrder o_) @ (((F.String " ") :: fmtCallpats l_)))));;
        let rec callpatsToString (L.Callpats l_) =
          F.makestring_fmt ((F.HVbox (fmtCallpats l_)));;
        let rec fmtROrder (L.RedOrder (p_, o_, o'_)) =
          begin
          match p_
          with 
               | less_
                   -> (fmtOrder o_) @ (((F.String " < ") :: fmtOrder o'_))
               | leq_
                   -> (fmtOrder o_) @ (((F.String " <= ") :: fmtOrder o'_))
               | eq_ -> (fmtOrder o_) @ (((F.String " = ") :: fmtOrder o'_))
          end;;
        let rec rOrderToString_ r_ =
          F.makestring_fmt ((F.HVbox (fmtROrder r_)));;
        let rec rDeclToString (L.RDecl (r_, L.Callpats l_)) =
          F.makestring_fmt
          ((F.HVbox ((fmtROrder r_) @ (((F.String " ") :: fmtCallpats l_)))));;
        let rec tabledDeclToString (L.TabledDecl cid) =
          F.makestring_fmt
          ((F.HVbox [(F.String (I.conDecName (I.sgnLookup cid)))]));;
        let rec keepTableDeclToString (L.KeepTableDecl cid) =
          F.makestring_fmt
          ((F.HVbox [(F.String (I.conDecName (I.sgnLookup cid)))]));;
        end;;
    (* -bp *);;
    let tDeclToString = tDeclToString;;
    let callpatsToString = callpatsToString;;
    let rOrderToString_ = rOrderToString_;;
    (* -bp *);;
    let rDeclToString = rDeclToString;;
    (* -bp *);;
    let tabledDeclToString = tabledDeclToString;;
    let keepTableDeclToString = keepTableDeclToString;;
    end;;
(* local *);;
(* functor ThmPrint *);;
# 1 "src/thm/thmprint.sml.ml"
