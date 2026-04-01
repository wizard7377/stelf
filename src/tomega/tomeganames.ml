(* # 1 "src/tomega/tomeganames.sig.ml" *)
open! Basis
module Tomega = Lambda_.Tomega

(* Naming *)
(* Author: Carsten Schuermann *)
include Tomeganames_intf
(* # 1 "src/tomega/tomeganames.fun.ml" *)
open! Basis

(* Naming *)
(* Author: Carsten Schuermann *)
module TomegaNames : TOMEGANAMES = struct
  module T = Tomega
  module I = IntSyn

  let rec decName = function
    | psi_, T.UDec d_ -> T.UDec (Names.decName (T.coerceCtx psi_, d_))
    | psi_, T.PDec (x, f_, tc1_, tc2_) ->
        let (I.NDec x') = Names.decName (T.coerceCtx psi_, I.NDec x) in
        T.PDec (x', f_, tc1_, tc2_)
end

(* # 1 "src/tomega/tomeganames.sml.ml" *)
