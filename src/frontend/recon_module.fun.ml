open! Basis

module ReconModule (ReconModule__0 : sig
  (* Elaboration for module expressions *)
  (* Author: Kevin Watkins *)
  module Global : GLOBAL

  (*! structure IntSyn : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  (*! structure Paths' : PATHS !*)
  module ReconTerm' : RECON_TERM

  (*! sharing ReconTerm'.IntSyn = IntSyn !*)
  (*! sharing ReconTerm'.Paths = Paths' !*)
  module ModSyn' : MODSYN

  (*! sharing ModSyn'.IntSyn = IntSyn !*)
  module IntTree : TABLE
end) : RECON_MODULE = struct
  module ExtSyn = ReconTerm'

  (*! structure Paths = Paths' !*)
  module ModSyn = ModSyn'

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
  type nonrec inst = Names.namespace * eqn list -> eqn list

  let rec coninst ((ids, id, r1), tm, r2) (ns, eqns) =
    let qid = Names.Qid (ids, id) in
    begin match Names.constLookupIn (ns, qid) with
    | None ->
        error
          ( r1,
            "Undeclared identifier "
            ^ Names.qidToString (valOf (Names.constUndefIn (ns, qid))) )
    | Some cid -> (cid, External tm, r2) :: eqns
    (* this is wrong because constants in the sig being instantiated might incorrectly appear in tm -kw *)
    end

  let rec addStructEqn (rEqns, r1, r2, ids, mid1, mid2) =
    let ns1 = Names.getComponents mid1 in
    let ns2 = Names.getComponents mid2 in
    let rec push eqn = rEqns := eqn :: !rEqns in
    let rec doConst (name, cid1) =
      begin match Names.constLookupIn (ns2, Names.Qid ([], name)) with
      | None ->
          error
            ( r1,
              "Instantiating structure lacks component "
              ^ Names.qidToString (Names.Qid (rev ids, name)) )
      | Some cid2 -> push (cid1, Internal cid2, r2)
      end
    in
    let rec doStruct (name, mid1) =
      begin match Names.structLookupIn (ns2, Names.Qid ([], name)) with
      | None ->
          error
            ( r1,
              "Instantiating structure lacks component "
              ^ Names.qidToString (Names.Qid (rev ids, name)) )
      | Some mid2 -> addStructEqn (rEqns, r1, r2, name :: ids, mid1, mid2)
      end
    in
    begin
      Names.appConsts doConst ns1;
      Names.appStructs doStruct ns1
    end

  let rec strinst ((ids, id, r1), strexp, r3) (ns, eqns) =
    let qid = Names.Qid (ids, id) in
    let mid1 =
      begin match Names.structLookupIn (ns, qid) with
      | None ->
          error
            ( r1,
              "Undeclared structure "
              ^ Names.qidToString (valOf (Names.structUndefIn (ns, qid))) )
      | Some mid1 -> mid1
      end
    in
    let mid2, r2 = strexp () in
    let rEqns = ref eqns in
    begin
      addStructEqn (rEqns, r2, r3, [], mid1, mid2);
      !rEqns
    end

  type nonrec whereclause = Names.namespace -> eqn list

  type nonrec sigexp =
    ModSyn.module_ option -> ModSyn.module_ * whereclause list

  let rec thesig (Some module_) = (module_, [])

  let rec sigid (id, r) None =
    begin match ModSyn.lookupSigDef id with
    | None -> error (r, "Undefined signature " ^ id)
    | Some module_ -> (module_, [])
    end

  let rec wheresig (sigexp, instList) moduleOpt =
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
      | (Internal cid, r), Condec_ -> (
          try
            ModSyn.strictify
              (ExtSyn.internalInst
                 (Condec_, ModSyn.abbrevify (cid, IntSyn.sgnLookup cid), r))
          with
          | ExtSyn.Error msg ->
              raise
                (ExtSyn.Error
                   ((msg ^ "\nin instantiation generated for ")
                   ^ Names.qidToString (Names.constQid cid)))
          | (External tm, r), Condec_ ->
              ModSyn.strictify (ExtSyn.externalInst (Condec_, tm, r)))
    in
    let rec transformConDec (cid, Condec_) =
      begin match IntTree.lookup table cid with
      | None -> Condec_
      | Some { contents = l } -> List.foldr doInst Condec_ l
      end
    in
    transformConDec

  let rec moduleWhere (module_, wherecl) =
    let mark, markStruct = IntSyn.sgnSize () in
    let module' = ModSyn.instantiateModule (module_, applyEqns wherecl) in
    let _ = Names.resetFrom (mark, markStruct) in
    module'
  (* val _ = IntSyn.resetFrom (mark, markStruct) *)
end
