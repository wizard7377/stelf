open! Basis;;
(* Theorem Declarations *);;
(* Author: Carsten Schuermann *);;
(* Modified: Brigitte Pientka, Frank Pfenning *);;
module type THM = sig
                  module ThmSyn : THMSYN
                  (*! structure Paths : PATHS !*)
                  exception Error of string 
                  val
                    installTotal : (ThmSyn.tDecl_ *
                                    (Paths.region * Paths.region list)) ->
                                   IntSyn.cid
                                   list
                  val uninstallTotal : IntSyn.cid -> bool
                  val
                    installTerminates : (ThmSyn.tDecl_ *
                                         (Paths.region * Paths.region list)) ->
                                        IntSyn.cid
                                        list
                  val uninstallTerminates : IntSyn.cid -> bool
                  (* true: was declared, false not *)
                  val
                    installReduces : (ThmSyn.rDecl_ *
                                      (Paths.region * Paths.region list)) ->
                                     IntSyn.cid
                                     list
                  val uninstallReduces : IntSyn.cid -> bool
                  val installTabled : ThmSyn.tabledDecl_ -> unit
                  val installKeepTable : ThmSyn.keepTableDecl_ -> unit
                  end;;
(* signature THM *);;