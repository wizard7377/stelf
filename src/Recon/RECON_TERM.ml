module type RECON_TERM = sig
  (*! structure IntSyn : INTSYN !*)
  module M : S.S
  module Cst = M.Cst
  module Ast = M.Ast
  module Paths = M.Paths
  module Syntax = M.Syntax

  exception Error of string

  val resetErrors : string -> unit

  (* filename -fp *)
  val checkErrors : Paths.region -> unit

  type traceMode = Progressive | Omniscient

  val trace : bool ref
  val traceMode : traceMode ref

  (* Reconstruction jobs *)
  type job

  val jnothing : job
  val jand : job * job -> job
  val jwithctx : Cst.decl Ast.ctx * job -> job
  val jterm : Cst.term -> job
  val jclass : Cst.term -> job
  val jof : Cst.term * Cst.term -> job

  type job_ =
    | JNothing
    | JAnd of job_ * job_
    | JWithCtx of Ast.dec Ast.ctx * job_
    | JTerm of (Ast.exp * Paths.occExp) * Ast.exp * Ast.uni
    | JClass of (Ast.exp * Paths.occExp) * Ast.uni
    | JOf of (Ast.exp * Paths.occExp) * (Ast.exp * Paths.occExp) * Ast.uni

  val recon : job -> job_
  val reconQuery : job -> job_
  val termRegion : Cst.term -> Paths.region
  val decRegion : Cst.decl -> Paths.region
  val ctxRegion : Cst.decl Ast.ctx -> Paths.region option

  (* unimplemented for the moment *)
  val internalInst : 'a -> 'b
  val externalInst : 'a -> 'b
end
