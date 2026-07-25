module type SIM = sig
  module CstA : CST.CST
  module CstB : CST.CST

  val sim_term : CstA.View.Term.t -> CstB.View.Term.t -> bool
  val sim_decl : CstA.View.Decl.t -> CstB.View.Decl.t -> bool
end
