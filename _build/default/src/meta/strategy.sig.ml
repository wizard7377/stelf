open! Basis;;
(* MTPStrategy : Version 1.3 *);;
(* Author: Carsten Schuermann *);;
module type MTPSTRATEGY = sig
                          module StateSyn : STATESYN
                          val
                            run : StateSyn.state_
                                  list ->
                                  StateSyn.state_ list * StateSyn.state_ list
                          end;;
(* open cases -> remaining cases * solved cases *);;
(* signature MTPSTRATEGY *);;