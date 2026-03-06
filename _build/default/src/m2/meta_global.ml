# 1 "src/m2/meta_global.sig.ml"
open! Basis;;
(* Global parameters *);;
(* Author: Carsten Schuermann *);;
module type METAGLOBAL = sig
                         type strategy_ = | Rfs 
                                          | Frs 
                         val strategy : strategy_ ref
                         val maxFill : int ref
                         val maxSplit : int ref
                         val maxRecurse : int ref
                         end;;
(* signature METAGLOBAL *);;
# 1 "src/m2/meta_global.fun.ml"

# 1 "src/m2/meta_global.sml.ml"
open! Basis;;
(* Global parameters *);;
(* Author: Carsten Schuermann *);;
module MetaGlobal : METAGLOBAL =
  struct
    type strategy_ = | Rfs 
                     | Frs ;;
    let strategy = ref Frs;;
    let maxFill = ref 6;;
    let maxSplit = ref 2;;
    let maxRecurse = ref 10;;
    end;;
(* structure MetaGlobal *);;