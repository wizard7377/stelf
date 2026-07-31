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

module type RECON_MODE = sig
  module M : S.S
  module Cst = M.Cst
  module Ast = M.Ast
  module Paths = M.Paths
  module Modes = Modes.Modesyn.ModeSyn

  exception Error of string

  val modeToMode : Cst.modeDec -> (Ast.cid * Modes.modeSpine) * Paths.region
end
