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

module type RECON_CONDEC = sig
  module M : S.S
  module Cst = M.Cst
  module Ast = M.Ast
  module Paths = M.Paths

  exception Error of string

  val condecToConDec :
    Cst.conDec * Paths.location * bool ->
    Ast.conDec option * Paths.occConDec option

  (* optional ConDec is absent for anonymous definitions *)
  (* bool = true means that condec is an abbreviation *)
end
