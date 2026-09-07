open! Intsyn
open! Intsyn.Lambda_
open! Names.Names_

(* # 1 "src/tomega/Tomeganames.sig.ml" *)
module Tomega = Lambda_.Tomega

(* Naming *)
(* Author: Carsten Schuermann *)
include TOMEGANAMES

(* # 1 "src/tomega/Tomeganames.fun.ml" *)

(* Naming *)
(* Author: Carsten Schuermann *)
module TomegaNames : TOMEGANAMES = struct
  module T = Tomega
  module I = IntSyn

  let decName a b = match a, b with
    | psi, T.UDec d_ -> T.UDec (Names.decName (T.coerceCtx psi) d_)
    | psi, T.PDec (x, f_, tc1, tc2) ->
        let (I.NDec x') = Names.decName (T.coerceCtx psi) (I.NDec x) in
        T.PDec (x', f_, tc1, tc2)
end

(* # 1 "src/tomega/Tomeganames.sml.ml" *)
