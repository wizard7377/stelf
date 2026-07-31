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

module type RECON_CONDEC = RECON_CONDEC.RECON_CONDEC

exception Error of string

module Make_ReconConDec
    (M : S.S)
    (RT : RECON_TERM.RECON_TERM with module M = M) :
  RECON_CONDEC with module M = M = struct
  module M = M
  module Cst = M.Cst
  module Ast = M.Ast
  module Paths = M.Paths

  exception Error = Error

  let error (r, msg) = raise (Error (Paths.wrap (r, msg)))

  (* Build an IntSyn context from a list of Cst.decl values. *)
  let makectx decls =
    let rec go ctx = function
      | [] -> ctx
      | d :: rest -> go (IntSyn.Decl (ctx, d)) rest
    in
    go IntSyn.Null decls

  (* Convert an IntSyn.dec ctx to a list (preserving order). *)
  let ctxToList ctx =
    let rec go acc = function
      | IntSyn.Null -> acc
      | IntSyn.Decl (g, d) -> go (d :: acc) g
    in
    go [] ctx

  let ctxAppend g1 g2 =
    let rec go = function
      | IntSyn.Null -> g1
      | IntSyn.Decl (g', d) -> IntSyn.Decl (go g', d)
    in
    go g2

  let ctxBlockToString (g0, (g1, g2)) =
    ignore (Names.varReset IntSyn.Null);
    let g0' = Names.ctxName g0 in
    let g1' = Names.ctxLUName g1 in
    let g2' = Names.ctxLUName g2 in
    let some_part =
      match g1' with
      | IntSyn.Null -> ""
      | _ -> "some " ^ Print.ctxToString (g0', g1') ^ "\n"
    in
    Print.ctxToString (IntSyn.Null, g0')
    ^ "\n" ^ some_part ^ "pi "
    ^ Print.ctxToString (ctxAppend g0' g1', g2')

  let checkFreevars (g0, (g1, g2), r) =
    match g0 with
    | IntSyn.Null -> ()
    | _ ->
        ignore (Names.varReset IntSyn.Null);
        let g0' = Names.ctxName g0 in
        let g1' = Names.ctxLUName g1 in
        let g2' = Names.ctxLUName g2 in
        error
          ( r,
            "Free variables in context block after term reconstruction:\n"
            ^ ctxBlockToString (g0', (g1', g2')) )

  (* Fresh names for anonymous top-level declarations: each `_` names a
     distinct constant (cf. the classic Twelf `- : A.` clause idiom, where
     every `-` shadows the previous one; here they get distinct generated
     names instead).  Collision-checked against the signature so a
     user-written `_1` etc. is never captured. *)
  let anon_counter = ref 0

  let fresh_anon_name () =
    let rec next () =
      incr anon_counter;
      let candidate = "_" ^ string_of_int !anon_counter in
      match Names.constLookup (Names.Qid ([], candidate)) with
      | None -> candidate
      | Some _ -> next ()
    in
    next ()

  let condecToConDec (condec, loc, abbFlag) =
    let (Paths.Loc (filename, r)) = loc in
    match Cst.View.ConDec.view condec with
    | Cst.View.ConDec.ConstantDecl (_, decl) ->
        (* Case A: %sort / %term  — constant type declaration *)
        let names, tm =
          match Cst.View.Decl.view decl with
          | Cst.View.Decl.Decl1 (_, names, tm, _) -> (names, tm)
          | Cst.View.Decl.Decl0 (_, names, tm) -> (names, tm)
          | _ -> assert false
        in
        let name =
          (* Callers (Impl.ml's %sort/%term handlers) split a multi-name
             decl into one single-name ConDec_ per name before it reaches
             here, so [names] is always a singleton in practice. *)
          let rec find_name = function
            | [] -> fresh_anon_name ()
            | None :: rest -> find_name rest
            | Some n :: _ -> n
          in
          find_name names
        in
        ignore (Names.varReset IntSyn.Null);
        ignore (RT.resetErrors filename);
        let (RT.JClass ((v_, oc), l_)) = RT.recon (RT.jclass tm) in
        ignore (RT.checkErrors r);
        let i, v'_ =
          try Abstract.abstractDecImp v_
          with Abstract.Error msg ->
            raise (Abstract.Error (Paths.wrap (r, msg)))
        in
        let cd =
          Names.nameConDec
            (IntSyn.ConDec (name, None, i, IntSyn.Normal, v'_, l_))
        in
        let ocd = Paths.dec (i, oc) in
        let _ =
          Display.chatter_s 3 ~kind:Display.Response
            (Print.conDecToString cd ^ "\n")
        in
        let _ =
          if !Global.doubleCheck then
            begin try Typecheck.Typecheck_.TypeCheck.check (v'_, IntSyn.Uni l_)
            with Typecheck.Typecheck_.TypeCheck.Error msg ->
              Printf.eprintf "DOUBLE-CHECK FAIL on ConDec %s: %s\n%!" name msg;
              raise (Typecheck.Typecheck_.TypeCheck.Error msg)
            end
        in
        (Some cd, Some ocd)
    | Cst.View.ConDec.ConstantDef (_, name, tm1, tm2_opt) ->
        (* Case B: constant definition / abbreviation *)
        ignore (Names.varReset IntSyn.Null);
        ignore (RT.resetErrors filename);
        let f =
          match tm2_opt with
          | None -> RT.jterm tm1
          | Some tm2 -> RT.jof (tm1, tm2)
        in
        let f' = RT.recon f in
        let (u_, oc1), (v_, oc2_opt), l_ =
          match f' with
          | RT.JTerm ((u_, oc1), v_, l_) -> ((u_, oc1), (v_, None), l_)
          | RT.JOf ((u_, oc1), (v_, oc2), l_) -> ((u_, oc1), (v_, Some oc2), l_)
          | _ -> assert false
        in
        ignore (RT.checkErrors r);
        let i, (u'', v'') =
          try Abstract.abstractDef (u_, v_)
          with Abstract.Error msg ->
            raise (Abstract.Error (Paths.wrap (r, msg)))
        in
        let opt_name = if name = "_" then None else Some name in
        let ocd = Paths.def (i, oc1, oc2_opt) in
        let cd =
          if abbFlag then
            Names.nameConDec (IntSyn.AbbrevDef (name, None, i, u'', v'', l_))
          else begin
            Typecheck.Typecheck_.Strict.check ((u'', v''), None);
            Names.nameConDec
              (IntSyn.ConDef (name, None, i, u'', v'', l_, IntSyn.ancestor u''))
          end
        in
        let _ =
          Display.chatter_s 3 ~kind:Display.Response
            (Print.conDecToString cd ^ "\n")
        in
        let _ =
          if !Global.doubleCheck then begin
            (try Typecheck.Typecheck_.TypeCheck.check (v'', IntSyn.Uni l_)
             with Typecheck.Typecheck_.TypeCheck.Error msg ->
               Printf.eprintf "DOUBLE-CHECK FAIL on ConDef %s (type): %s\n%!"
                 name msg;
               raise (Typecheck.Typecheck_.TypeCheck.Error msg));
            try Typecheck.Typecheck_.TypeCheck.check (u'', v'')
            with Typecheck.Typecheck_.TypeCheck.Error msg ->
              Printf.eprintf "DOUBLE-CHECK FAIL on ConDef %s (term): %s\n%!"
                name msg;
              raise (Typecheck.Typecheck_.TypeCheck.Error msg)
          end
        in
        (Option.map (fun _ -> cd) opt_name, Some ocd)
    | Cst.View.ConDec.BlockDecl (_, name, lsome, lblock) ->
        (* Case C: block declaration *)
        let gsome = makectx lsome in
        let gblock = makectx lblock in
        let r' =
          match (RT.ctxRegion gsome, RT.ctxRegion gblock) with
          | Some r1, Some r2 -> Paths.join (r1, r2)
          | _, Some r2 -> r2
          | Some r1, None -> r1
          | None, None -> r
        in
        ignore (Names.varReset IntSyn.Null);
        ignore (RT.resetErrors filename);
        let j = RT.jwithctx (gsome, RT.jwithctx (gblock, RT.jnothing)) in
        let (RT.JWithCtx (gsome_, RT.JWithCtx (gblock_, _))) = RT.recon j in
        ignore (RT.checkErrors r);
        let g0_, ctxs =
          try Abstract.abstractCtxs [ gsome_; gblock_ ]
          with Constraints.Error c_ ->
            error
              ( r',
                "Constraints remain in context block after term reconstruction:\n"
                ^ ctxBlockToString (IntSyn.Null, (gsome_, gblock_))
                ^ "\n" ^ Print.cnstrsToString c_ )
        in
        let gsome', gblock' =
          match ctxs with [ a; b ] -> (a, b) | _ -> assert false
        in
        ignore (checkFreevars (g0_, (gsome', gblock'), r'));
        let bd =
          Names.nameConDec
            (IntSyn.BlockDec (name, None, gsome', ctxToList gblock'))
        in
        let _ =
          Display.chatter_s 3 ~kind:Display.Response
            (Print.conDecToString bd ^ "\n")
        in
        (Some bd, None)
    | Cst.View.ConDec.BlockDef (_, name, worlds) ->
        (* Case D: block definition *)
        let w' = List.map (fun (ids, id) -> Names.Qid (ids, id)) worlds in
        let cids =
          List.map
            (function
              | qid -> (
                  match Names.constLookup qid with
                  | None ->
                      raise
                        (Names.Error
                           ("Undeclared label "
                           ^ Names.qidToString (valOf (Names.constUndef qid))
                           ^ "."))
                  | Some cid -> cid))
            w'
        in
        let bd = Names.nameConDec (IntSyn.BlockDef (name, None, cids)) in
        let _ =
          Display.chatter_s 3 ~kind:Display.Response
            (Print.conDecToString bd ^ "\n")
        in
        (Some bd, None)
    | _ -> raise (Error "condecToConDec: unrecognised conDec variant")
end
