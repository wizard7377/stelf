open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Cover
open! Cover.Cover_
open! Formatter
open! Formatter__Formatter_
open! Names
open! Names.Names_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Subordinate
open! Subordinate
open! Meta
open! Meta.Meta_
open! Modes
open! Modes.Modes_
open! Trail
open! Trail.Trail_

(* # 1 "src/tomega/Tomeganames.sig.ml" *)
open! Basis
module Tomega = Lambda_.Tomega

(* Naming *)
(* Author: Carsten Schuermann *)
include TOMEGANAMES

(* # 1 "src/tomega/Tomeganames.fun.ml" *)
open! Basis

(* Naming *)
(* Author: Carsten Schuermann *)
module TomegaNames : TOMEGANAMES = struct
  module T = Tomega
  module I = IntSyn

  let decName = function
    | psi, T.UDec d_ -> T.UDec (Names.decName (T.coerceCtx psi, d_))
    | psi, T.PDec (x, f_, tc1, tc2) ->
        let (I.NDec x') = Names.decName (T.coerceCtx psi, I.NDec x) in
        T.PDec (x', f_, tc1, tc2)
end

(* # 1 "src/tomega/Tomeganames.sml.ml" *)
