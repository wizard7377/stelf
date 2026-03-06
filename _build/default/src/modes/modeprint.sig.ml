open! Basis;;
(* Printing Mode Declarations *);;
(* Author: Carsten Schuermann *);;
module type MODEPRINT = sig
                        (*! structure ModeSyn : MODESYN !*)
                        val
                          modeToString : (IntSyn.cid * ModeSyn.modeSpine_) ->
                                         string
                        val
                          modesToString : (IntSyn.cid * ModeSyn.modeSpine_)
                                          list ->
                                          string
                        end;;
(* signature MODEPRINT *);;