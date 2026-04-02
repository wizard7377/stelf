(* # 1 "src/frontend/ReconThm.sig.ml" *)
open! Basis

(* External Syntax for meta theorems *)
(* Author: Carsten Schuermann *)

module type THMEXTSYN = sig
  module ExtSyn : ReconTerm_intf.EXTSYN

  (*! structure Paths : PATHS  !*)
  type order

  val varg : Paths.region * string list -> order
  val lex : Paths.region * order list -> order
  val simul : Paths.region * order list -> order

  type callpats

  val callpats : (string * string option list * Paths.region) list -> callpats

  type tdecl

  val tdecl : order * callpats -> tdecl

  (* -bp *)
  type predicate

  val predicate : string * Paths.region -> predicate

  (* -bp *)
  type rdecl

  val rdecl : predicate * order * order * callpats -> rdecl

  type tableddecl

  val tableddecl : string * Paths.region -> tableddecl

  type keepTabledecl

  val keepTabledecl : string * Paths.region -> keepTabledecl

  type prove

  val prove : int * tdecl -> prove

  type establish

  val establish : int * tdecl -> establish

  type assert_

  val assert_ : callpats -> assert_

  type decs
  type theorem
  type theoremdec

  val null : decs
  val decl : decs * ExtSyn.dec -> decs
  val top : theorem
  val exists : decs * theorem -> theorem
  val forall : decs * theorem -> theorem
  val forallStar : decs * theorem -> theorem
  val forallG : (decs * decs) list * theorem -> theorem
  val dec : string * theorem -> theoremdec

  (* world checker *)
  type wdecl

  val wdecl : (string list * string) list * callpats -> wdecl
end

module type RECON_THM = sig
  module ThmSyn : Thmsyn.THMSYN
  include THMEXTSYN

  exception Error of string

  val tdeclTotDecl : tdecl -> ThmSyn.tDecl * (Paths.region * Paths.region list)
  val rdeclTorDecl : rdecl -> ThmSyn.rDecl * (Paths.region * Paths.region list)
  val tableddeclTotabledDecl : tableddecl -> ThmSyn.tabledDecl * Paths.region

  val keepTabledeclToktDecl :
    keepTabledecl -> ThmSyn.keepTableDecl * Paths.region

  val theoremToTheorem : theorem -> ThmSyn.thDecl
  val theoremDecToTheoremDec : theoremdec -> string * ThmSyn.thDecl
  val proveToProve : prove -> ThmSyn.pDecl * (Paths.region * Paths.region list)

  val establishToEstablish :
    establish -> ThmSyn.pDecl * (Paths.region * Paths.region list)

  val assertToAssert : assert_ -> ThmSyn.callpats * Paths.region list
  val wdeclTowDecl : wdecl -> ThmSyn.wDecl * Paths.region list
end
