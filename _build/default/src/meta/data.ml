# 1 "src/meta/data.sig.ml"
open! Basis;;
(* Data aquired during proof search *);;
(* Author: Carsten Schuermann *);;
module type MTPDATA = sig val maxFill : int ref end;;
(* signature MTPDATA *);;
# 1 "src/meta/data.fun.ml"
open! Basis;;
(* Meta Global parameters *);;
(* Author: Carsten Schuermann *);;
module MTPData(MTPData__0: sig module MTPGlobal : MTPGLOBAL end) : MTPDATA =
  struct
    let maxFill = ref 0;;
    end;;
(* structure MTPData*);;
# 1 "src/meta/data.sml.ml"
