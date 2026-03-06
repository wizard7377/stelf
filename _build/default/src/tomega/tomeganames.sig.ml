open! Basis;;
(* Naming *);;
(* Author: Carsten Schuermann *);;
module type TOMEGANAMES = sig
                          val
                            decName : (Tomega.dec_ IntSyn.ctx_ * Tomega.dec_) ->
                                      Tomega.dec_
                          end;;