open! Basis

module type RECON_MODE = sig
  module M : S.S
  module Cst = M.Cst
  module Ast = M.Ast
  module Paths = M.Paths
  module Modes = Modes.Modesyn.ModeSyn

  exception Error of string

  val modeToMode : Cst.modeDec -> (Ast.cid * Modes.modeSpine) * Paths.region
end
