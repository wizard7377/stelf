module type RECON_MODULE = RECON_MODULE.RECON_MODULE

exception Error of string

module Make_ReconModule
    (M : S.S)
    (RT : RECON_TERM.RECON_TERM with module M = M) :
  RECON_MODULE with module M = M = struct
  module M = M
  module Cst = M.Cst
  module Ast = M.Ast
  module Paths = M.Paths
  module ModSyn = Modules.Modules_.ModSyn
  module IntTree = TableInstances.IntRedBlackTree

  exception Error = Error

  let error (r, msg) = raise (Error (Paths.wrap (r, msg)))

  type inst_ = External of Cst.term | Internal of IntSyn.cid
  type eqn = IntSyn.cid * inst_ * Paths.region
  type whereclause = ModSyn.Names.namespace -> eqn list

  type structDec =
    | StructDec of string option * ModSyn.module_ * whereclause list
    | StructDef of string option * Ast.mid

  let strexpToStrexp se =
    match Cst.View.Struct.StrExp.view se with
    | Cst.View.Struct.StrExp.StrExp (loc, (ids, id)) -> (
        let qid = ModSyn.Names.Qid (ids, id) in
        match ModSyn.Names.structLookup qid with
        | None ->
            raise
              (Error
                 ("Undeclared structure "
                 ^ ModSyn.Names.qidToString
                     (valOf (ModSyn.Names.structUndef qid))))
        | Some mid -> mid)

  let rec sigexpToSigexp (se, module_opt) =
    match Cst.View.Struct.SigExp.view se with
    | Cst.View.Struct.SigExp.SigId (_, id) -> (
        match ModSyn.lookupSigDef id with
        | None -> raise (Error ("Undefined signature " ^ id))
        | Some module_ -> (module_, []))
    | Cst.View.Struct.SigExp.WhereSig (_, inner_se, insts) ->
        let module_, wherecls = sigexpToSigexp (inner_se, module_opt) in
        let wherecl ns =
          let rec go = function
            | [] -> []
            | inst :: rest -> (
                let eqns = go rest in
                match Cst.View.Struct.Inst.view inst with
                | Cst.View.Struct.Inst.ConInst (loc, (ids, id), _, tm) -> (
                    let r = Cst.loc_to_region loc in
                    let qid = ModSyn.Names.Qid (ids, id) in
                    match ModSyn.Names.constLookupIn (ns, qid) with
                    | None ->
                        error
                          ( r,
                            "Undeclared identifier "
                            ^ ModSyn.Names.qidToString
                                (valOf (ModSyn.Names.constUndefIn (ns, qid))) )
                    | Some cid -> (cid, External tm, r) :: eqns)
                | Cst.View.Struct.Inst.StrInst (loc, (ids, id), _, strexp) ->
                    let r1 = Cst.loc_to_region loc in
                    let qid = ModSyn.Names.Qid (ids, id) in
                    let mid1 =
                      match ModSyn.Names.structLookupIn (ns, qid) with
                      | None ->
                          error
                            ( r1,
                              "Undeclared structure "
                              ^ ModSyn.Names.qidToString
                                  (valOf (ModSyn.Names.structUndefIn (ns, qid)))
                            )
                      | Some mid1 -> mid1
                    in
                    let mid2 = strexpToStrexp strexp in
                    let rEqns = ref eqns in
                    addStructEqn (rEqns, r1, r1, [], mid1, mid2);
                    !rEqns
                | _ -> assert false)
          in
          go insts
        in
        (module_, wherecls @ [ wherecl ])
    | _ -> (
        match module_opt with
        | Some module_ -> (module_, [])
        | None -> raise (Error "sigexpToSigexp: unrecognised sigexp"))

  and addStructEqn (rEqns, r1, r2, ids, mid1, mid2) =
    let ns1 = ModSyn.Names.getComponents mid1 in
    let ns2 = ModSyn.Names.getComponents mid2 in
    let doConst (name, cid1) =
      match ModSyn.Names.constLookupIn (ns2, ModSyn.Names.Qid ([], name)) with
      | None ->
          error
            ( r1,
              "Instantiating structure lacks component "
              ^ ModSyn.Names.qidToString (ModSyn.Names.Qid (List.rev ids, name))
            )
      | Some cid2 -> rEqns := (cid1, Internal cid2, r2) :: !rEqns
    in
    let doStruct (name, mid1') =
      match ModSyn.Names.structLookupIn (ns2, ModSyn.Names.Qid ([], name)) with
      | None ->
          error
            ( r1,
              "Instantiating structure lacks component "
              ^ ModSyn.Names.qidToString (ModSyn.Names.Qid (List.rev ids, name))
            )
      | Some mid2' -> addStructEqn (rEqns, r1, r2, name :: ids, mid1', mid2')
    in
    ModSyn.Names.appConsts doConst ns1;
    ModSyn.Names.appStructs doStruct ns1

  let sigdefToSigdef (sd, module_opt) =
    let name_opt, sigexp =
      match Cst.View.Struct.SigDef.view sd with
      | Cst.View.Struct.SigDef.SigDef (_, name_opt, sigexp) -> (name_opt, sigexp)
      | _ -> assert false
    in
    let module_, wherecls = sigexpToSigexp (sigexp, module_opt) in
    (name_opt, module_, wherecls)

  let structdecToStructDec (sd, module_opt) =
    match Cst.View.Struct.StructDec.view sd with
    | Cst.View.Struct.StructDec.StructDecl (_, name_opt, sigexp) ->
        let module_, wherecls = sigexpToSigexp (sigexp, module_opt) in
        StructDec (name_opt, module_, wherecls)
    | Cst.View.Struct.StructDec.StructDef (_, name_opt, strexp) ->
        let mid = strexpToStrexp strexp in
        StructDef (name_opt, mid)
    | _ -> raise (Error "structdecToStructDec: unrecognised structDec")

  type eqnTable = (inst_ * Paths.region) list ref IntTree.table

  let applyEqns wherecl namespace =
    let eqns = wherecl namespace in
    let table : eqnTable = IntTree.new_ 0 in
    let add (cid, inst_, r) =
      match IntTree.lookup table cid with
      | None -> IntTree.insert table (cid, ref [ (inst_, r) ])
      | Some rl -> rl := (inst_, r) :: !rl
    in
    ignore (List.app add eqns);
    let doInst ((inst_, r), conDec_) =
      match inst_ with
      | Internal cid -> (
          try
            ModSyn.strictify
              (RT.internalInst
                 (conDec_, ModSyn.abbrevify (cid, IntSyn.sgnLookup cid), r))
          with RT.Error msg ->
            raise
              (RT.Error
                 (msg ^ "\nin instantiation generated for "
                 ^ ModSyn.Names.qidToString (ModSyn.Names.constQid cid))))
      | External tm -> ModSyn.strictify (RT.externalInst (conDec_, tm, r))
    in
    let transformConDec (cid, conDec_) =
      match IntTree.lookup table cid with
      | None -> conDec_
      | Some { contents = l } -> List.foldr doInst conDec_ l
    in
    transformConDec

  let moduleWhere (module_, wherecl) =
    let mark, markStruct = IntSyn.sgnSize () in
    let module' = ModSyn.instantiateModule (module_, applyEqns wherecl) in
    ignore (Names.resetFrom (mark, markStruct));
    module'
end
