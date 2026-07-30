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
  type t

  val jnothing : t
  val jand : t * t -> t
  val jwithctx : Cst.decl Ast.ctx * t -> t
  val jterm : Cst.term -> t
  val jclass : Cst.term -> t
  val jof : Cst.term * Cst.term -> t

  type result =
    | JNothing
    | JAnd of result * result
    | JWithCtx of Ast.dec Ast.ctx * result
    | JTerm of (Ast.exp * Paths.occExp) * Ast.exp * Ast.uni
    | JClass of (Ast.exp * Paths.occExp) * Ast.uni
    | JOf of (Ast.exp * Paths.occExp) * (Ast.exp * Paths.occExp) * Ast.uni

  val recon : t -> result
  val reconQuery : t -> result
  val termRegion : Cst.term -> Paths.region
  val decRegion : Cst.decl -> Paths.region
  val ctxRegion : Cst.decl Ast.ctx -> Paths.region option

  (* unimplemented for the moment *)
  val internalInst : 'a -> 'b
  val externalInst : 'a -> 'b
end
