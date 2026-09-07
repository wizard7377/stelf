open! Basis

module type RECON_QUERY = sig
  module M : S.S
  module Cst = M.Cst
  module Ast = M.Ast
  module Paths = M.Paths

  exception Error of string

  val queryToQuery :
    Cst.query -> Paths.location ->
    Ast.exp * string option * (Ast.exp * string) list

  (* (A, SOME(""X""), [(Y1, ""Y1""),...] *)
  (* where A is query type, X the optional proof term variable name *)
  (* Yi the EVars in the query and ""Yi"" their names *)
  val solveToSolve :
    Cst.define list -> Cst.solve -> Paths.location ->
    Ast.exp * (Ast.exp -> (Ast.conDec * Paths.occConDec option) list)
end
