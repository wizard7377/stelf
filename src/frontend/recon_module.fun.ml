open! Basis

module ReconModule (ReconModule__0 : sig
  (* Elaboration for module expressions *)
  (* Author: Kevin Watkins *)
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  (*! structure Paths' : PATHS !*)
  module ReconTerm' : Recon_term.RECON_TERM

  (*! sharing ReconTerm'.IntSyn = IntSyn !*)
  (*! sharing ReconTerm'.Paths = Paths' !*)
  module ModSyn' : Modsyn.MODSYN with module Names = Names

  (*! sharing ModSyn'.IntSyn = IntSyn !*)
  module IntTree : TABLE with type key = IntSyn.cid
end) : RECON_MODULE with module ModSyn = ReconModule__0.ModSyn' = struct
  module ExtSyn = ReconModule__0.ReconTerm'
  module Names = ReconModule__0.Names
  module IntTree = ReconModule__0.IntTree

  (*! structure Paths = Paths' !*)
  module ModSyn = ReconModule__0.ModSyn'

  exception Error of string

  let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))

  type nonrec strexp = unit -> IntSyn.mid * Paths.region

  let rec strexp (ids, id, r) () =
    let qid = Names.Qid (ids, id) in
    begin match Names.structLookup qid with
    | None ->
        error
          ( r,
            "Undeclared structure "
            ^ Names.qidToString (valOf (Names.structUndef qid)) )
    | Some mid -> (mid, r)
    end

  let rec strexpToStrexp (f : strexp) = (fun (r, _) -> r) (f ())

  type inst_ = External of ExtSyn.term | Internal of IntSyn.cid
  type nonrec eqn = IntSyn.cid * inst_ * Paths.region
  type nonrec inst = ModSyn.Names.namespace * eqn list -> eqn list

  let rec coninst ((ids, id, r1), tm, r2) : inst = fun (ns, eqns) ->
    let qid = ModSyn.Names.Qid (ids, id) in
    begin match ModSyn.Names.constLookupIn (ns, qid) with
    | None ->
        error
          ( r1,
            "Undeclared identifier "
            ^ ModSyn.Names.qidToString (valOf (ModSyn.Names.constUndefIn (ns, qid))) )
    | Some cid -> (cid, External tm, r2) :: eqns
    (* this is wrong because constants in the sig being instantiated might incorrectly appear in tm -kw *)
    end

  let rec addStructEqn (rEqns, r1, r2, ids, mid1, mid2) =
    let ns1 = ModSyn.Names.getComponents mid1 in
    let ns2 = ModSyn.Names.getComponents mid2 in
    let rec push eqn = rEqns := eqn :: !rEqns in
    let rec doConst (name, cid1) =
      begin match ModSyn.Names.constLookupIn (ns2, ModSyn.Names.Qid ([], name)) with
      | None ->
          error
            ( r1,
              "Instantiating structure lacks component "
              ^ Names.qidToString (ModSyn.Names.Qid (rev ids, name)) )
      | Some cid2 -> push (cid1, Internal cid2, r2)
      end
    in
    let rec doStruct (name, mid1) =
      begin match ModSyn.Names.structLookupIn (ns2, ModSyn.Names.Qid ([], name)) with
      | None ->
          error
            ( r1,
              "Instantiating structure lacks component "
              ^ Names.qidToString (ModSyn.Names.Qid (rev ids, name)) )
      | Some mid2 -> addStructEqn (rEqns, r1, r2, name :: ids, mid1, mid2)
      end
    in
    begin
      ModSyn.Names.appConsts doConst ns1;
      ModSyn.Names.appStructs doStruct ns1
    end

  let rec strinst ((ids, id, r1), strexp, r3) : inst = fun (ns, eqns) ->
    let qid = ModSyn.Names.Qid (ids, id) in
    let mid1 =
      begin match ModSyn.Names.structLookupIn (ns, qid) with
      | None ->
          error
            ( r1,
              "Undeclared structure "
              ^ Names.qidToString (valOf (ModSyn.Names.structUndefIn (ns, qid))) )
      | Some mid1 -> mid1
      end
    in
    let mid2, r2 = strexp () in
    let rEqns = ref eqns in
    begin
      addStructEqn (rEqns, r2, r3, [], mid1, mid2);
      !rEqns
    end

  type nonrec whereclause = ModSyn.Names.namespace -> eqn list

  type nonrec sigexp =
    ModSyn.module_ option -> ModSyn.module_ * whereclause list

  let rec thesig (Some module_) = (module_, [])

  let rec sigid (id, r) None =
    begin match ModSyn.lookupSigDef id with
    | None -> error (r, "Undefined signature " ^ id)
    | Some module_ -> (module_, [])
    end

  let rec wheresig (sigexp, instList) : sigexp = fun moduleOpt ->
    let module_, wherecls = sigexp moduleOpt in
    let rec wherecl ns =
      foldr (function inst, eqns -> inst (ns, eqns)) [] instList
    in
    (module_, wherecls @ [ wherecl ])

  let rec sigexpToSigexp (sigexp, moduleOpt) = sigexp moduleOpt

  type nonrec sigdef =
    ModSyn.module_ option -> string option * ModSyn.module_ * whereclause list

  let rec sigdef (idOpt, sigexp) moduleOpt =
    let module_, wherecls = sigexp moduleOpt in
    (idOpt, module_, wherecls)

  let rec sigdefToSigdef (sigdef, moduleOpt) = sigdef moduleOpt

  type structDec_ =
    | StructDec of string option * ModSyn.module_ * whereclause list
    | StructDef of string option * IntSyn.mid

  type nonrec structdec = ModSyn.module_ option -> structDec_

  let rec structdec (idOpt, sigexp) moduleOpt =
    let module_, inst = sigexp moduleOpt in
    StructDec (idOpt, module_, inst)

  let rec structdef (idOpt, strexp) None =
    let mid = strexpToStrexp strexp in
    StructDef (idOpt, mid)

  let rec structdecToStructDec (structdec, moduleOpt) = structdec moduleOpt

  type nonrec eqnTable = (inst_ * Paths.region) list ref IntTree.table_

  let rec applyEqns wherecl namespace =
    let eqns = wherecl namespace in
    let table : eqnTable = IntTree.new_ 0 in
    let rec add (cid, inst_, r) =
      begin match IntTree.lookup table cid with
      | None -> IntTree.insert table (cid, ref [ (inst_, r) ])
      | Some rl -> rl := (inst_, r) :: !rl
      end
    in
    let _ = List.app add eqns in
    let rec doInst = function
      | (Internal cid, r), conDec_ ->
          begin
            try
              ModSyn.strictify
                (ExtSyn.internalInst
                   (conDec_, ModSyn.abbrevify (cid, IntSyn.sgnLookup cid), r))
            with
            | ExtSyn.Error msg ->
                raise
                  (ExtSyn.Error
                     ((msg ^ "\nin instantiation generated for ")
                     ^ Names.qidToString (Names.constQid cid)))
          end
      | (External tm, r), conDec_ ->
          ModSyn.strictify (ExtSyn.externalInst (conDec_, tm, r))
    in
    let rec transformConDec (cid, conDec_) =
      begin match IntTree.lookup table cid with
      | None -> conDec_
      | Some { contents = l } -> List.foldr doInst conDec_ l
      end
    in
    transformConDec

  let rec moduleWhere : ModSyn.module_ * whereclause -> ModSyn.module_ = function
    | module_, wherecl ->
    let mark, markStruct = IntSyn.sgnSize () in
    let module' = ModSyn.instantiateModule (module_, applyEqns wherecl) in
    let _ = Names.resetFrom (mark, markStruct) in
    module'
  (* val _ = IntSyn.resetFrom (mark, markStruct) *)
end
