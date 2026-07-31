open! Basis
open! Global
open! Global.Global_
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Table
open! Table.Table_
open! Msg
open! Msg.Msg_
open! Print
open! Print.Print_
open! Debug

module type RECON_THM = sig
  module M : S.S
  module Cst = M.Cst
  module Ast = M.Ast
  module Paths = M.Paths
  module ThmSyn : Thm.Thmsyn.THMSYN

  exception Error of string

  val tdeclTotDecl :
    Cst.View.Thm.TDecl.t -> ThmSyn.tDecl * (Paths.region * Paths.region list)

  val rdeclTorDecl :
    Cst.View.Thm.RDecl.t -> ThmSyn.rDecl * (Paths.region * Paths.region list)

  val tableddeclTotabledDecl :
    Cst.View.Thm.TabledDecl.t -> ThmSyn.tabledDecl * Paths.region

  val keepTabledeclToktDecl :
    Cst.View.Thm.KeepTableDecl.t -> ThmSyn.keepTableDecl * Paths.region

  val theoremToTheorem : Cst.View.Thm.Thm.t -> ThmSyn.thDecl
  val theoremDecToTheoremDec : Cst.View.Thm.ThmDec.t -> string * ThmSyn.thDecl

  val proveToProve :
    Cst.View.Thm.Prove.t -> ThmSyn.pDecl * (Paths.region * Paths.region list)

  val establishToEstablish :
    Cst.View.Thm.Establish.t ->
    ThmSyn.pDecl * (Paths.region * Paths.region list)

  val assertToAssert :
    Cst.View.Thm.Assert.t -> ThmSyn.callpats * Paths.region list

  val wdeclTowDecl : Cst.View.Thm.WDecl.t -> ThmSyn.wDecl * Paths.region list
end
