open! Basis;;
(* External Syntax for meta theorems *);;
(* Author: Carsten Schuermann *);;
module type THMEXTSYN = sig
                        module ExtSyn : EXTSYN
                        (*! structure Paths : PATHS  !*)
                        type nonrec order
                        val varg : (Paths.region * string list) -> order
                        val lex : (Paths.region * order list) -> order
                        val simul : (Paths.region * order list) -> order
                        type nonrec callpats
                        val
                          callpats : (string *
                                      string
                                      option
                                      list *
                                      Paths.region)
                                     list ->
                                     callpats
                        type nonrec tdecl
                        val tdecl : (order * callpats) -> tdecl
                        (* -bp *)
                        type nonrec predicate
                        val predicate : (string * Paths.region) -> predicate
                        (* -bp *)
                        type nonrec rdecl
                        val
                          rdecl : (predicate * order * order * callpats) ->
                                  rdecl
                        type nonrec tableddecl
                        val
                          tableddecl : (string * Paths.region) -> tableddecl
                        type nonrec keepTabledecl
                        val
                          keepTabledecl : (string * Paths.region) ->
                                          keepTabledecl
                        type nonrec prove
                        val prove : (int * tdecl) -> prove
                        type nonrec establish
                        val establish : (int * tdecl) -> establish
                        type nonrec assert_
                        val assert_ : callpats -> assert_
                        type nonrec decs
                        type nonrec theorem
                        type nonrec theoremdec
                        val null : decs
                        val decl : (decs * ExtSyn.dec) -> decs
                        val top : theorem
                        val exists : (decs * theorem) -> theorem
                        val forall : (decs * theorem) -> theorem
                        val forallStar : (decs * theorem) -> theorem
                        val
                          forallG : ((decs * decs) list * theorem) -> theorem
                        val dec : (string * theorem) -> theoremdec
                        (* world checker *)
                        type nonrec wdecl
                        val
                          wdecl : ((string list * string) list * callpats) ->
                                  wdecl
                        end;;
(*  val wdecl : (decs * decs) list * callpats -> wdecl *);;
(* signature THMEXTSYN *);;
module type RECON_THM = sig
                        module ThmSyn : THMSYN
                        include THMEXTSYN
                        exception Error of string 
                        val
                          tdeclTotDecl : tdecl ->
                                         ThmSyn.tDecl_ *
                                         (Paths.region * Paths.region list)
                        val
                          rdeclTorDecl : rdecl ->
                                         ThmSyn.rDecl_ *
                                         (Paths.region * Paths.region list)
                        val
                          tableddeclTotabledDecl : tableddecl ->
                                                   ThmSyn.tabledDecl_ *
                                                   Paths.region
                        val
                          keepTabledeclToktDecl : keepTabledecl ->
                                                  ThmSyn.keepTableDecl_ *
                                                  Paths.region
                        val theoremToTheorem : theorem -> ThmSyn.thDecl_
                        val
                          theoremDecToTheoremDec : theoremdec ->
                                                   string * ThmSyn.thDecl_
                        val
                          proveToProve : prove ->
                                         ThmSyn.pDecl_ *
                                         (Paths.region * Paths.region list)
                        val
                          establishToEstablish : establish ->
                                                 ThmSyn.pDecl_ *
                                                 (Paths.region *
                                                  Paths.region
                                                  list)
                        val
                          assertToAssert : assert_ ->
                                           ThmSyn.callpats_ *
                                           Paths.region
                                           list
                        val
                          wdeclTowDecl : wdecl ->
                                         ThmSyn.wDecl_ * Paths.region list
                        end;;
(* signature RECON_THM *);;