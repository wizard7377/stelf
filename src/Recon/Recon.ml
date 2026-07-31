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
open ReconConDec
open ReconMode
open ReconModule
open ReconQuery
open ReconThm
open ReconTerm

module type RECON = RECON.RECON
module type RECON_TERM = RECON_TERM.RECON_TERM
module type RECON_THM = RECON_THM.RECON_THM
module type RECON_CONDEC = RECON_CONDEC.RECON_CONDEC
module type RECON_MODE = RECON_MODE.RECON_MODE
module type RECON_MODULE = RECON_MODULE.RECON_MODULE
module type RECON_QUERY = RECON_QUERY.RECON_QUERY

module Make_Recon (M : S.S) = struct
  include M
  module Ast = M.Ast
  module Cst = M.Cst

  module ReconTerm =
    Make_ReconTerm
      (M)
      (struct
        module Names = Names
        module Approx = Approx
        module Whnf = Whnf
        module Unify = UnifyTrail
        module Abstract = Abstract
        module Print = Print
        module StringTree = TableInstances.StringRedBlackTree
        module Msg = Msg
        module CsManager = Solvers.CsManager
      end)

  module ReconThm = Make_ReconThm (M) (ReconTerm)
  module ReconConDec = Make_ReconConDec (M) (ReconTerm)
  module ReconMode = Make_ReconMode (M)
  module ReconModule = Make_ReconModule (M) (ReconTerm)
  module ReconQuery = Make_ReconQuery (M) (ReconTerm)
end
