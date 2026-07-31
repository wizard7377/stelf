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

module type S = sig
  module Paths : Paths.PATHS.PATHS
  module Cst : Cst.CST with module Paths = Paths
  module Syntax : Syntax.SYNTAX
  module Ast = Intsyn.IntSyn
end
