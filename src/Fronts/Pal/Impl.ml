open! Basis

type source = Fpath.t option

let source_to_string = function
  | None -> "<INTERACTIVE>"
  | Some p -> Fpath.to_string p

let string_to_source = function
  | "<INTERACTIVE>" -> None
  | s -> Some (Fpath.of_string s)

module Impl () = struct

  let current_path : string list ref = ref []
  let current_load_path : Fpath.t list ref = ref ([Result.get_ok @@ Bos.OS.Dir.current ()])
  let load_paths : (Fpath.t * string) list ref = ref []


  (** Additional directories to search for included files. *)
  (* Save Basis's OS before any module definitions shadow it *)
  module BasisOS = OS

  (* ------------------------------------------------------------------ *)
  (* Module wiring                                                         *)
  (* ------------------------------------------------------------------ *)

  (* Capture the concrete Paths instance before the alias shadows Paths.   *)
  module PathsConcrete = Paths.Paths_.Paths

  (* Ascribe Paths to the bare PATHS signature so it matches what         *)
  (* Make_Cst and Make_Recon's S.S both expect.                           *)
  module Paths : Paths.PATHS.PATHS = Paths.Paths_

  (* Create our own Cst from the same ascribed Paths so that              *)
  (* Cst.Paths = Paths and Recon.Cst.Paths = Paths, giving consistent     *)
  (* type-sharing across the entire pipeline.                              *)
  module Cst = Cst.Make_Cst (Paths)
  module Names = Modern.Modern.Names
  module Syntax = Syntax.IntSyn (Global.Global_.Global)
  module Parser = Parsing.Parser.Parser

  (* Force Cst/Names/Paths sharing so Cmd and load_string agree on types *)
  (* Make_Modern is transparent (no return-type seal), so OCaml infers    *)
  (* ModernImpl.Cst = Cst, ModernImpl.Paths = Paths, etc.                  *)
  module ModernImpl = Modern.Make_Modern (Paths) (Cst) (Names) (Parser)
  module Cmd = Modern.Cmd.Make_Cmd (ModernImpl)

  (* Elaboration layer.  All sub-modules are currently stubs that raise   *)
  (* descriptive errors.  install1 bypasses them with failwith.           *)
  module Recon = Recon.Make_Recon (struct
    module Paths = Paths
    module Cst = Cst
    module Syntax = Syntax
    module Ast = Intsyn.IntSyn
  end)

  (* ------------------------------------------------------------------ *)
  (* Source and mode                                                       *)
  (* ------------------------------------------------------------------ *)

  type source = File of Fpath.t | Input of string

  let mode : [ `Repl | `Lsp | `Other ] ref = ref `Other

  (* ------------------------------------------------------------------ *)
  (* Global flags                                                          *)
  (* ------------------------------------------------------------------ *)

  let chatter = Global.Global_.Global.chatter
  let double_check = Global.Global_.Global.doubleCheck
  let unsafe = Global.Global_.Global.unsafe
  let auto_freeze = Global.Global_.Global.autoFreeze
  let time_limit = Global.Global_.Global.timeLimit

  (* ------------------------------------------------------------------ *)
  (* Status                                                               *)
  (* ------------------------------------------------------------------ *)

  type status = Ok | Abort

  let status_to_exit = function Ok -> 0 | Abort -> 1

  (* Top-level namespace for the group currently being loaded.
     %require deposits here, escaping any inner %scope. *)
  let current_group_ns : Names.namespace ref = ref (Names.newNamespace ())

  (* Canonical paths already run via %require; skip on repeat (#once). *)
  let required_files : (string, unit) Hashtbl.t = Hashtbl.create 16

  (* Forward reference set after `load` is defined, breaking the cycle
     between Install.install1 (needs to call load for %require) and load
     (which calls Install.install). *)
  let load_file_ref : (Names.namespace -> Fpath.t -> status) ref =
    ref (fun _ns _path -> Ok)

  (* Forward reference for TOML config detection, set after Config is defined.
     load calls this to check if a file is a valid TOML project before
     treating it as source. *)
  let try_toml_ref : (Fpath.t -> string -> Project.Format.file option) ref =
    ref (fun _path _str -> None)

  let load_toml_ref : (Project.Format.file -> status) ref =
    ref (fun _cfg -> Ok)

  (* ------------------------------------------------------------------ *)
  (* Options store                                                         *)
  (* ------------------------------------------------------------------ *)

  module Options = struct
    let tbl : (string, string) Hashtbl.t = Hashtbl.create 16
    let get k = Hashtbl.find_opt tbl k
    let set k v = Hashtbl.replace tbl k v
  end

  (* ------------------------------------------------------------------ *)
  (* Helpers                                                              *)
  (* ------------------------------------------------------------------ *)

  (* let msg s = Msg.Msg_.Msg.message s *)

  let msg m =
    Display.message ~level:Display.Normal ~kind:Display.Response
      (Display.Form.string m)

  let dbg m =
    Display.message ~level:Display.Exhaustive ~kind:Display.Debug
      (Display.Form.string m)

  let print_error (label : string) (detail : string) : unit =
    Display.message ~level:Display.Normal ~kind:Display.Error
      (Display.Form.string (label ^ ": " ^ detail))

  (* ------------------------------------------------------------------ *)
  (* ConDec installation                                                   *)
  (* ------------------------------------------------------------------ *)

  let install_condec ns (cd : Intsyn.IntSyn.conDec) : unit =
    let open Intsyn.IntSyn in
    let cid = sgnAdd cd in
    Names.installConstName cid;
    Names.insertConst (ns, cid);
    match cd with
    | BlockDec _ -> Subordinate.Subordinate_.Subordinate.installBlock cid
    | BlockDef _ -> ()
    | _ ->
        Index.Index_.Index.install Ordinary (Const cid);
        Compile.Compile_.Compile.install Ordinary cid;
        Subordinate.Subordinate_.Subordinate.install cid;
        Subordinate.Subordinate_.Subordinate.installDef cid

  (* ------------------------------------------------------------------ *)
  (* Install module                                                        *)
  (* ------------------------------------------------------------------ *)

  module ModeTable = Modes.Modes_.ModeTable
  module ModeCheck = Modes.Modes_.ModeCheck
  module ModeDec = Modes.Modedec.MakeModeDec ()
  module UniqueTable = Unique.Unique_.UniqueTable
  module Unique = Unique.Unique_.Unique
  module WorldSyn = Worldcheck.Worldcheck_.WorldSyn
  module ModSyn = Modules.Modules_.ModSyn
  module ThmInst = Thm.Thm_.Thm
  module ThmSyn = Thm.Thm_.ThmSyn
  module ThmTotal = Cover.Cover_.Total
  module Cover = Cover.Cover_.Cover

  let rec factor_sort : Cst.decl list -> Cst.term = function
    | [] -> Cst.Term.typ ()
    | decl :: decls -> Cst.Term.pi [ decl ] (factor_sort decls)

  module Install = struct
    let unfold_app tm =
      let rec go acc = function
        | Cst.App_ (_, f, arg) -> go (arg :: acc) f
        | head -> (head, acc)
      in
      go [] tm

    let term_to_name = function
      | Cst.Ucid_ (_, "_", _) -> None
      | Cst.Ucid_ (_, n, _) -> Some n
      | Cst.Lcid_ (_, n, _) -> Some n
      | Cst.Evar_ (n, _) -> Some n
      | Cst.Fvar_ (n, _) -> Some n
      | _ -> None

    let term_to_head = function
      | Cst.Ucid_ (_, n, _) | Cst.Lcid_ (_, n, _) -> n
      | _ ->
          failwith
            "%total/%terminates: expected identifier as call-pattern head"

    let build_thm_rdecl pred_str body =
      let module TS = ThmSyn in
      let pred, swap =
        match pred_str with
        | "=" -> (TS.Eq, false)
        | "<" -> (TS.Less, false)
        | "<=" -> (TS.Leq, false)
        | ">" -> (TS.Less, true)
        | ">=" -> (TS.Leq, true)
        | s -> failwith ("%reduces: unknown predicate " ^ s)
      in
      let term_to_order tm = TS.Varg [ term_to_head tm ] in
      let o_out, o_in, body_rest =
        match body with
        | out_tm :: in_tm :: rest ->
            (term_to_order out_tm, term_to_order in_tm, rest)
        | _ ->
            failwith
              "%reduces: expected predicate, two order arguments, and call \
               patterns"
      in
      let o1, o2 = if swap then (o_in, o_out) else (o_out, o_in) in
      let term_to_cp tm =
        let head, args = unfold_app tm in
        let name = term_to_head head in
        let cid =
          match Names.constLookup (Names.Qid ([], name)) with
          | None ->
              failwith
                ("%reduces: undeclared identifier " ^ name ^ " in call pattern")
          | Some c -> c
        in
        (cid, List.map term_to_name args)
      in
      let callpats = TS.Callpats (List.map term_to_cp body_rest) in
      let dummy_r = PathsConcrete.Reg (0, 0) in
      let rrs = (dummy_r, List.map (fun _ -> dummy_r) body_rest) in
      (TS.RDecl (TS.RedOrder (pred, o1, o2), callpats), rrs)

    let build_thm_tdecl label (orders : Cst.order list) body =
      let module TS = ThmSyn in
      let rec cst_to_thm = function
        | Cst.Varg_ (_, names) -> TS.Varg names
        | Cst.Lex_ (_, ords) -> TS.Lex (List.map cst_to_thm ords)
        | Cst.Simul_ (_, ords) -> TS.Simul (List.map cst_to_thm ords)
      in
      let order =
        match orders with
        | [] -> TS.Varg []
        | [ o ] -> cst_to_thm o
        | many -> TS.Simul (List.map cst_to_thm many)
      in
      let term_to_cp tm =
        let head, args = unfold_app tm in
        let name = term_to_head head in
        let cid =
          match Names.constLookup (Names.Qid ([], name)) with
          | None ->
              failwith
                (label ^ ": undeclared identifier " ^ name ^ " in call pattern")
          | Some c -> c
        in
        (cid, List.map term_to_name args)
      in
      let callpats = TS.Callpats (List.map term_to_cp body) in
      let dummy_r = PathsConcrete.Reg (0, 0) in
      let rrs = (dummy_r, List.map (fun _ -> dummy_r) body) in
      (TS.TDecl (order, callpats), rrs)

    let loc_of filename (l : Cst.loc) : Paths.location =
      Paths.Loc (filename, Cst.loc_to_region l)

    let decl_loc (Cst.Dec_ (_, _, l)) : Cst.loc = l

    let term_loc (tm : Cst.term) : Cst.loc =
      match tm with
      | Cst.Arrow_ (l, _, _) | Cst.Pi_ (l, _, _) | Cst.Lam_ (l, _, _)
      | Cst.App_ (l, _, _) | Cst.Hastype_ (l, _, _) | Cst.Omitted_ l
      | Cst.Typ_ l | Cst.MacroParam_ (l, _, _) | Cst.Local_ (l, _, _) -> l
      | Cst.Lcid_ (_, _, l) | Cst.Ucid_ (_, _, l) | Cst.Quid_ (_, _, l)
      | Cst.Scon_ (_, l) | Cst.Evar_ (_, l) | Cst.Fvar_ (_, l) -> l

    let run_query loc q =
      let v_, opt_name, xs_ =
        Recon.ReconQuery.queryToQuery (q, loc)
      in
      let g =
        Compile.Compile_.Compile.compileGoal (Intsyn.IntSyn.Null, v_)
      in
      let solutions = ref 0 in
      let exception Done in
      let sc m_ =
        incr solutions;
        if !Global.Global_.Global.chatter >= 3 then begin
          msg
            (Printf.sprintf "---------- Solution %d ----------\n" !solutions);
          List.app
            (fun (e_, n) ->
              msg
                (n ^ " = "
                ^ Print.Print_.expToString (Intsyn.IntSyn.Null, e_)
                ^ "\n"))
            xs_;
          match opt_name with
          | None -> ()
          | Some name ->
              msg
                (name ^ " = "
                ^ Print.Print_.expToString (Intsyn.IntSyn.Null, m_)
                ^ "\n")
        end;
        raise Done
      in
      (try
         Opsem.Opsem_.AbsMachine.solve
           ( (g, Intsyn.IntSyn.id),
             Compile.CompSyn.CompSyn.DProg
               (Intsyn.IntSyn.Null, Intsyn.IntSyn.Null),
             sc )
       with Done -> ());
      if !solutions = 0 && !Global.Global_.Global.chatter >= 3 then
        msg "No solution.\n"

    let install_worlds_cmd ids tms =
      let resolve_block id =
        match Names.constLookup (Names.Qid ([], id)) with
        | None ->
            failwith
              ("Undeclared block label " ^ id ^ " in worlds declaration")
        | Some cid -> cid
      in
      let rec flatten = function
        | [] -> []
        | cid :: rest -> (
            match Intsyn.IntSyn.sgnLookup cid with
            | Intsyn.IntSyn.BlockDec _ -> cid :: flatten rest
            | Intsyn.IntSyn.BlockDef (_, _, l) -> flatten (l @ rest)
            | _ -> cid :: flatten rest)
      in
      let block_cids = flatten (List.map resolve_block ids) in
      let w_ = Intsyn.Lambda_.Tomega.Worlds block_cids in
      let lookup_head tm =
        match Cst.View.Term.view tm with
        | Cst.View.Term.Lowercase (_, (ns, n)) ->
            Names.constLookup (Names.Qid (ns, n))
        | Cst.View.Term.Uppercase (_, (ns, n)) ->
            Names.constLookup (Names.Qid (ns, n))
        | Cst.View.Term.Qualified (_, (ns, n)) ->
            Names.constLookup (Names.Qid (ns, n))
        | _ -> None
      in
      let resolve_family tm =
        let family_cid_opt =
          match Cst.View.Term.view tm with
          | Cst.View.Term.App (_, head, _) -> lookup_head head
          | v -> lookup_head (Cst.View.Term.review v)
        in
        match family_cid_opt with
        | None -> failwith "%worlds: expected a type family name"
        | Some a -> a
      in
      let families = List.map resolve_family tms in
      List.app (fun a -> WorldSyn.install (a, w_)) families;
      List.app (fun a -> WorldSyn.worldcheck w_ a) families

    let install_condec_cmd ?(inline = false) ns condec loc =
      match Recon.ReconConDec.condecToConDec (condec, loc, inline) with
      | Some cd, _ -> install_condec ns cd
      | None, _ -> ()

    let name_to_cid ns label id =
      match Names.constLookupIn (ns, Names.Qid ([], id)) with
      | None ->
          failwith
            ("Undeclared identifier " ^ id ^ " in " ^ label ^ " declaration")
      | Some cid -> cid

    let rec install1 ?(path = None) ns (cmd : Cst.cmd) : unit =
      let filename =
        Stdlib.Option.value
          (Option.map Fpath.to_string path)
          ~default:"<INTERACTIVE>"
      in
      Debug.(
        msg' ~src:Group.pal ~level:Level.Debug Fmt.string "Installing command");
      match cmd with
      | Cst.SortCmd_ (ids, decls) ->
          let sort_loc = match decls with d :: _ -> decl_loc d | [] -> Cst.ghost in
          List.app
            (fun id ->
              Debug.(
                msg' ~src:Group.pal ~level:Level.Debug
                  Fmt.(const string "Installing sort" ++ sp ++ string)
                  id);
              let kind = factor_sort decls in
              let condec =
                Cst.ConDec.constant_decl (Cst.Decl.decl1 [ Some id ] kind)
              in
              install_condec_cmd ns condec (loc_of filename sort_loc))
            ids
      | Cst.TermCmd_ decl -> (
          Debug.(
            msg' ~src:Group.pal ~level:Level.Debug Fmt.string
              "Installing term command");

          let names, ty =
            match Cst.View.Decl.view decl with
            | Cst.View.Decl.Decl1 (_, ns, t, _) -> (ns, t)
            | Cst.View.Decl.Decl0 (_, ns, t) -> (ns, t)
          in
          let names' = List.map (function Some n -> n | None -> "_") names in
          Display.message ~level:Display.Detailed
            Display.(
              string "Installing term command for"
              ++ each string names' ++ space ()
              ++ hvbox [ shown Cst.show_term ty ]);
          let condec = Cst.ConstantDecl_ decl in
          install_condec_cmd ns condec (loc_of filename (decl_loc decl)))
      | Cst.DefineCmd_ (Cst.Define_ (name_opt, tm, tp_opt)) ->
          let name = match name_opt with Some n -> n | None -> "_" in
          let condec = Cst.ConstantDef_ (name, tm, tp_opt) in
          install_condec_cmd ns condec (loc_of filename (term_loc tm))
      | Cst.QueryCmd_ (_n, _b, _d, (Cst.Query_ (_, qtm) as q)) ->
          run_query (loc_of filename (term_loc qtm)) q
      | Cst.SolveCmd_ (Cst.Solve_ (_, stm) as sol) ->
          let v_, sc_fn =
            Recon.ReconQuery.solveToSolve ([], sol, loc_of filename (term_loc stm))
          in
          let g =
            Compile.Compile_.Compile.compileGoal (Intsyn.IntSyn.Null, v_)
          in
          let exception Done of Intsyn.IntSyn.exp in
          let sc m_ = raise (Done m_) in
          let m_ =
            match
              try
                Opsem.Opsem_.AbsMachine.solve
                  ( (g, Intsyn.IntSyn.id),
                    Compile.CompSyn.CompSyn.DProg
                      (Intsyn.IntSyn.Null, Intsyn.IntSyn.Null),
                    sc );
                None
              with Done m_ -> Some m_
            with
            | None -> failwith "%solve: no solution found"
            | Some m_ -> m_
          in
          List.app (fun (cd, _) -> install_condec ns cd) (sc_fn m_)
      | Cst.StopCmd_ -> ()
      | Cst.QuitCmd_ -> BasisOS.Process.exit BasisOS.Process.success
      | Cst.HelpCmd_ topic ->
          begin match topic with
          | None ->
              msg
                "Commands: sort, term, query, define, solve, quit, help, get, \
                 set, version\n"
          | Some t -> msg (("No help available for '" ^ t) ^ "'\n")
          end
      | Cst.GetCmd_ key ->
          begin match Options.get key with
          | Some v -> msg ((key ^ " = ") ^ v ^ "\n")
          | None -> msg (key ^ " is not set\n")
          end
      | Cst.SetCmd_ (key, value) -> Options.set key value
      | Cst.VersionCmd_ -> msg (Frontend.Version.Version.version_string ^ "\n")
      | Cst.EvalCmd_ cmds -> List.app (install1 ~path ns) cmds
      | Cst.AdhocQueryCmd_ (Cst.Query_ (_, qtm) as q) ->
          run_query (loc_of filename (term_loc qtm)) q
      | Cst.DeclCmd_ tm ->
          let qid_opt =
            match Cst.View.Term.view tm with
            | Cst.View.Term.Lowercase (_, (ns, n)) -> Some (Names.Qid (ns, n))
            | Cst.View.Term.Uppercase (_, (ns, n)) -> Some (Names.Qid (ns, n))
            | Cst.View.Term.Qualified (_, (ns, n)) -> Some (Names.Qid (ns, n))
            | _ -> None
          in
          begin match qid_opt with
          | None -> msg "decl: expected an identifier\n"
          | Some qid ->
              begin match Names.constLookup qid with
              | None -> msg (Names.qidToString qid ^ " has not been declared\n")
              | Some cid ->
                  let condec = Intsyn.IntSyn.sgnLookup cid in
                  msg (Print.Print_.conDecToString condec ^ "\n")
              end
          end
      | Cst.FreezeCmd_ ids ->
          let cids = List.map (name_to_cid ns "freeze") ids in
          let _ = Subordinate.Subordinate_.Subordinate.freeze cids in
          ()
      | Cst.ThawCmd_ ids ->
          if not !unsafe then failwith "%thaw not safe: Toggle `unsafe' flag";
          let cids = List.map (name_to_cid ns "thaw") ids in
          let _ = Subordinate.Subordinate_.Subordinate.thaw cids in
          ()
      | Cst.DeterministicCmd_ ids ->
          let cids = List.map (name_to_cid ns "deterministic") ids in
          List.app
            (fun cid -> Compile.CompSyn.CompSyn.detTableInsert (cid, true))
            cids
      | Cst.PrecCmd_ (fix, prec, ids) ->
          let p = Names.Fixity.Strength prec in
          let fixity =
            match fix with
            | Cst.Left_ -> Names.Fixity.Infix (p, Names.Fixity.Left)
            | Cst.Right_ -> Names.Fixity.Infix (p, Names.Fixity.Right)
            | Cst.Middle_ -> Names.Fixity.Infix (p, Names.Fixity.None)
            | Cst.Prefix_ -> Names.Fixity.Prefix p
            | Cst.Postfix_ -> Names.Fixity.Postfix p
            | Cst.FNone_ -> Names.Fixity.Nonfix
          in
          List.app
            (fun id ->
              let cid = name_to_cid ns "prec" id in
              Names.installFixity (cid, fixity))
            ids
      | Cst.SymbolCmd_ (pref, id) ->
          let cid = name_to_cid ns "symbol" id in
          Names.installAlias (pref, cid);
          Names.insertConstAlias (ns, pref, cid);
          Names.installNamePref (cid, ([ pref ], [ pref ]))
      | Cst.InlineCmd_ (name, tm) ->
          let condec = Cst.ConstantDef_ (name, tm, None) in
          install_condec_cmd ~inline:true ns condec (loc_of filename (term_loc tm))
      | Cst.BlockCmd_ (id, items) ->
          let pis =
            Stdlib.List.filter_map
              (function Cst.BlockPi_ d -> Some d | _ -> None)
              items
          in
          let somes =
            Stdlib.List.filter_map
              (function Cst.BlockSome_ d -> Some d | _ -> None)
              items
          in
          let block_loc =
            match pis @ somes with d :: _ -> decl_loc d | [] -> Cst.ghost
          in
          let condec = Cst.BlockDecl_ (id, pis, somes) in
          install_condec_cmd ns condec (loc_of filename block_loc)
      | Cst.ModeCmd_ md ->
          let () =
            Display.(
              message ~level:Detailed
                (string "Installing mode declaration for "
                ++ shown Cst.show_modeDec md))
          in
          let mdec, _r = Recon.ReconMode.modeToMode md in
          let cid, _ = mdec in
          (match ModeTable.modeLookup cid with
          | Some _ when Subordinate.Subordinate_.Subordinate.frozen [ cid ] ->
              failwith
                ("Cannot redeclare mode for frozen constant "
                ^ Names.qidToString (Names.constQid cid))
          | _ -> ());
          ModeTable.installMode mdec;
          ModeCheck.checkMode mdec
      | Cst.TotalCmd_ (intros, body) ->
          let t_, rrs = build_thm_tdecl "%total" intros body in
          let la_ = ThmInst.installTotal (t_, rrs) in
          List.app ThmTotal.install la_;
          List.app ThmTotal.checkFam la_
      | Cst.TerminatesCmd_ (intros, body) ->
          let t_, rrs = build_thm_tdecl "%terminates" intros body in
          let la_ = ThmInst.installTerminates (t_, rrs) in
          ignore la_
      | Cst.CoversCmd_ md ->
          let mdec, _r = Recon.ReconMode.modeToMode md in
          Cover.checkCovers mdec
      | Cst.NameCmd_ _id -> ()
      | Cst.ReducesCmd_ (pred_str, body) ->
          let r_, rrs = build_thm_rdecl pred_str body in
          let la_ = ThmInst.installReduces (r_, rrs) in
          List.app Terminate.Terminate_.Reduces.checkFamReduction la_
      | Cst.UniqueCmd_ tm ->
          let mdec_opt =
            match Cst.View.Term.view tm with
            | Cst.View.Term.Lowercase (_, (ns, n)) ->
                begin match Names.constLookup (Names.Qid (ns, n)) with
                | None -> None
                | Some cid -> Some (cid, Modes.Modesyn.ModeSyn.Mnil)
                end
            | _ -> None
          in
          begin match mdec_opt with
          | None -> msg "unique: expected a type family name\n"
          | Some ((cid, _) as mdec) ->
              UniqueTable.installMode mdec;
              Unique.checkUnique mdec
          end
      | Cst.UnionCmd_ (id, ids) ->
          let syms = List.map (fun s -> ([], s)) ids in
          let condec = Cst.BlockDef_ (id, syms) in
          install_condec_cmd ns condec (loc_of filename Cst.ghost)
      | Cst.WorldsCmd_ (ids, tms) -> install_worlds_cmd ids tms
      | Cst.QueryTabledCmd_ (numSol, try_, _d, (Cst.Query_ (_, qtm) as q)) ->
          let a_, opt_name, xs_ =
            Recon.ReconQuery.queryToQuery (q, loc_of filename (term_loc qtm))
          in
          let g =
            Compile.Compile_.Compile.compileGoal (Intsyn.IntSyn.Null, a_)
          in
          let solutions = ref 0 in
          let stages = ref 1 in
          let exception Done in
          let exceeds bound limit =
            match limit with None -> false | Some n -> bound >= n
          in
          let sc _o_ =
            incr solutions;
            if !chatter >= 3 then begin
              msg
                (Printf.sprintf "---------- Solution %d ----------\n" !solutions);
              List.app
                (fun (e_, n) ->
                  msg
                    (n ^ " = "
                    ^ Print.Print_.expToString (Intsyn.IntSyn.Null, e_)
                    ^ "\n"))
                xs_;
              match opt_name with
              | None -> ()
              | Some name ->
                  msg
                    (name ^ " = "
                    ^ Print.Print_.expToString (Intsyn.IntSyn.Null, a_)
                    ^ "\n")
            end;
            match numSol with
            | Some n when !solutions >= n -> raise Done
            | _ -> ()
          in
          let dprog =
            Compile.CompSyn.CompSyn.DProg
              (Intsyn.IntSyn.Null, Intsyn.IntSyn.Null)
          in
          let rec loop () =
            if exceeds (!stages - 1) try_ then raise Done;
            if Opsem.Opsem_.Tabled_.nextStage () then begin
              incr stages;
              loop ()
            end
          in
          Opsem.Opsem_.Tabled_.reset ();
          Opsem.Opsem_.Tabled_.fillTable ();
          (try
             Opsem.Opsem_.Tabled_.solve ((g, Intsyn.IntSyn.id), dprog, sc);
             loop ()
           with Done -> ());
          if !solutions = 0 && !chatter >= 3 then msg "No tabled solution.\n"
      | Cst.Open_ ids ->
          let qid =
            match List.rev ids with
            | [] -> failwith "%open: empty module path"
            | last :: prefix -> Names.Qid (List.rev prefix, last)
          in
          let mid =
            match Names.structLookupIn (ns, qid) with
            | Some m -> m
            | None ->
              (match Names.structLookup qid with
               | Some m -> m
               | None ->
                 failwith ("%open: unknown module " ^ Names.qidToString qid))
          in
          let comps = Names.getComponents mid in
          Names.appConsts (fun (_, cid) -> Names.insertConst (ns, cid)) comps;
          Names.appStructs (fun (_, m) -> Names.insertStruct (ns, m)) comps
      | Cst.Scope_ (name, body_cmd) ->
          let child_ns = Names.newNamespace () in
          let mid =
            Intsyn.IntSyn.sgnStructAdd (Intsyn.IntSyn.StrDec (name, None))
          in
          Names.installStructName mid;
          Names.insertStruct (ns, mid);
          install1 ~path child_ns body_cmd;
          Names.installComponents (mid, child_ns)
      | Cst.Use_ _ ->
          failwith
            "%use: module instantiation not yet implemented in this frontend"
      | Cst.Macro_ _ ->
          failwith "Macros not yet implemented in this frontend"
      | Cst.Seq_ cmds ->
          List.app (install1_item ~path ns) cmds
        | Cst.Require_ ids ->
          let rel = String.concatWith "/" ids in
          let req_path = Fpath.v rel in
          let parent_dir = Fpath.parent req_path in
          let stem = Fpath.to_string (Fpath.rem_ext (Fpath.base req_path)) in
          let is_source_ext ext = ext <> "" && ext <> ".cfg" && ext <> ".toml" in
          let found =
            Stdlib.List.find_map (fun base_dir ->
              let search_dir = Fpath.(base_dir // parent_dir) in
              match Bos.OS.Dir.contents search_dir with
              | Error _ -> None
              | Ok entries ->
                  Stdlib.List.find_opt (fun entry ->
                    let b = Fpath.base entry in
                    Fpath.to_string (Fpath.rem_ext b) = stem
                    && is_source_ext (Fpath.get_ext b)
                  ) entries
            ) !current_load_path
          in
          (match found with
          | None -> failwith ("%require: file not found: " ^ rel)
          | Some file_path ->
              let canon = Fpath.to_string (Fpath.normalize file_path) in
              dbg ("%%require: resolved " ^ rel ^ " -> " ^ canon);
              if not (Hashtbl.mem required_files canon) then begin
                dbg ("%%require: loading " ^ canon);
                Hashtbl.add required_files canon ();
                (match !load_file_ref !current_group_ns file_path with
                | Ok -> dbg ("%%require: finished " ^ canon)
                | Abort ->
                    failwith ("%require: error loading " ^ Fpath.to_string file_path))
              end else
                dbg ("%%require: skipping " ^ canon ^ " (already loaded)"))

    and install1_item ?(path = None) ns (item : Cst.item) : unit =
      match item with
      | Cst.Outer _ -> ()
      | Cst.Cmd cmd -> install1 ~path ns cmd

    let install ?(path = None) ns (cmds : Cst.cmd list) : unit =
      List.app (install1 ~path ns) cmds

    let reset () : unit = Frontend.Frontend_.Stelf.reset ()
  end

  (* ------------------------------------------------------------------ *)
  (* Loading                                                              *)
  (* ------------------------------------------------------------------ *)

  let load_string ?(path = None) ?(ns_init = None) (str : string) : status =
    dbg ("load_string: " ^ source_to_string path);
    let ns = match ns_init with Some r -> r | None -> ref (Names.newNamespace ()) in
    let loc = Cst.ghost in
    try
      let cmds = ModernImpl.run (Cmd.parse ()) ns loc str in
      try
        Install.install ~path !ns cmds;
        Ok
      with
      | Error.Error.Err _ as e -> raise e
      | Recon.ReconConDec.Error msg
      | Recon.ReconTerm.Error msg
      | Recon.ReconModule.Error msg
      | Recon.ReconQuery.Error msg ->
          Error.Error.err ~stage:Error.Error.Recon (Display.Form.string msg)
      | Recon.ReconMode.Error msg
      | Recon.ReconThm.Error msg ->
          Error.Error.err ~stage:Error.Error.Check (Display.Form.string msg)
      | Intsyn.Lambda_.Abstract.Error msg ->
          Error.Error.err ~stage:Error.Error.Recon (Display.Form.string msg)
      | Typecheck.Typecheck_.TypeCheck.Error msg ->
          Error.Error.err ~stage:Error.Error.Check
            Display.Form.(string ("Double-check failed (internal bug): " ^ msg))
      | Failure msg ->
          Error.Error.err ~stage:Error.Error.Unknown (Display.Form.string msg)
      | exn ->
          Error.Error.err ~stage:Error.Error.Unknown
            (Display.Form.string (Printexc.to_string exn))
    with
    | Error.Error.Err (stage, form) ->
        let stage_str =
          match stage with
          | Error.Error.Parse -> "parse"
          | Error.Error.Check -> "check"
          | Error.Error.Recon -> "recon"
          | _ -> "error"
        in
        Display.message ~level:Display.Normal ~kind:Display.Error
          (Display.Form.string
             ("[" ^ stage_str ^ "] " ^ Display.Form.to_plain form));
        Abort
    | Modern.Modern.ParseError e ->
        (* Fallback during transition; should no longer be reached *)
        print_error (source_to_string path) ("parse error: " ^ e);
        Abort
    | exn ->
        Error.Error.err ~stage:Error.Error.Unknown
          (Display.Form.string (Printexc.to_string exn))

  let load ns (src : source) : status =
    let ns_ref = ref ns in
    match src with
    | Input str ->
        dbg "load: loading from input";
        load_string ~ns_init:(Some ns_ref) str
    | File path -> (
        dbg ("load: loading file " ^ Fpath.to_string path);
        let filename = Some path in
        try
          let buf = Bos.OS.File.read path in
          let str = match buf with
          | Ok s -> s
          | Error (`Msg msg) ->
              print_error "pal" ("Failed to read file: " ^ msg);
              failwith (msg)
          in
          match !try_toml_ref path str with
          | Some cfg ->
              dbg ("load: detected TOML config in " ^ Fpath.to_string path);
              !load_toml_ref cfg
          | None ->
              let saved_load_path = !current_load_path in
              let parent = Fpath.parent path in
              current_load_path := parent :: !current_load_path;
              let result = load_string ~path:filename ~ns_init:(Some ns_ref) str in
              current_load_path := saved_load_path;
              result
        with exn ->
          print_error "pal" (Printexc.to_string exn);
          Abort)

  let () = load_file_ref := (fun ns fp -> load ns (File fp))

  let read_decl () : status =
    begin match TextIO.inputLine TextIO.stdIn with
    | Some line -> load_string ~path:None line
    | None -> Ok
    end

  let decl (name : string) : status =
    begin match Names.stringToQid name with
    | None ->
        msg (name ^ " is not a valid qualified identifier\n");
        Abort
    | Some qid ->
        begin match Names.constLookup qid with
        | None ->
            msg (name ^ " has not been declared\n");
            Abort
        | Some cid ->
            let condec = Intsyn.IntSyn.sgnLookup cid in
            msg (Print.Print_.conDecToString condec ^ "\n");
            Ok
        end
    end

  (* ------------------------------------------------------------------ *)
  (* Configuration file management                                        *)
  (* ------------------------------------------------------------------ *)

  module Config = struct 
    type t = Project.Format.file
    let read (src : source) : t =
      let str = match src with
      | Input str -> str
      | File path -> (
          try
            let ic = TextIO.openIn (Fpath.to_string path) in
            let str = TextIO.inputAll ic in
            let () = TextIO.closeIn ic in
            str
          with exn ->
            let msg = "Failed to read config file " ^ Fpath.to_string path
                      ^ ": " ^ Printexc.to_string exn in
            print_error "pal" msg;
            failwith msg) in
      let toml =
        match Otoml.Parser.from_string str with
        | toml -> toml
        | exception Otoml.Parse_error (pos_opt, msg) ->
            let loc = match pos_opt with
              | Some (line, col) -> Printf.sprintf " at line %d, col %d" line col
              | None -> "" in
            let full = Printf.sprintf "TOML parse error%s: %s" loc msg in
            print_error "pal" full;
            failwith full
        | exception exn ->
            let msg = "TOML parse error: " ^ Printexc.to_string exn in
            print_error "pal" msg;
            failwith msg in
      match Project.Format.from_toml toml with
      | Error msg ->
          print_error "pal" msg;
          failwith msg
      | Ok config -> config

      let rebase_group base_dir (g : Project.Format.t) : Project.Format.t =
        let open Project.Format in
        let rebase_dep = function
          | Local ({ path = Some p; _ } as d) -> Local { d with path = Some Fpath.(base_dir // p) }
          | dep -> dep
        in
        { g with
          main = Fpath.(base_dir // g.main);
          dirs = List.map (fun d -> Fpath.(base_dir // d)) g.dirs;
          deps = List.map rebase_dep g.deps;
        }

      let try_toml (path : Fpath.t) (str : string) : t option =
        let base_dir = Fpath.parent path in
        let is_toml = Fpath.has_ext "toml" path in
        match Otoml.Parser.from_string str with
        | exception Otoml.Parse_error (pos_opt, msg) ->
            if is_toml then begin
              let loc = match pos_opt with
                | Some (line, col) -> Printf.sprintf " at line %d, col %d" line col
                | None -> "" in
              print_error "config"
                (Printf.sprintf "TOML parse error in %s%s: %s" (Fpath.to_string path) loc msg)
            end;
            None
        | exception exn ->
            if is_toml then
              print_error "config"
                ("Error reading TOML config " ^ Fpath.to_string path ^ ": "
                 ^ Printexc.to_string exn);
            None
        | toml ->
            match Project.Format.from_toml toml with
            | Error msg ->
                if is_toml then
                  print_error "config" (Fpath.to_string path ^ ": " ^ msg);
                None
            | Ok cfg ->
                let groups = List.map (rebase_group base_dir) cfg.Project.Format.groups in
                Some { cfg with Project.Format.groups = groups }

      let rec load' ~(all_groups : Project.Format.t list) (cfg : Project.Format.t) : status =
        let open Project.Format in
        dbg ("Config.load': group " ^ cfg.name ^ ", main=" ^ Fpath.to_string cfg.main);
        let group_ns = Names.newNamespace () in
        let saved_group_ns = !current_group_ns in
        let saved_load_path = !current_load_path in
        current_group_ns := group_ns;
        current_load_path :=
          (if cfg.dirs = [] then [ Fpath.v "." ] else cfg.dirs);
        let install_dep dep =
          match dep with
          | Local { name; alias; path = None } ->
              dbg ("Config.load': dependency " ^ name
                ^ (match alias with Some a -> " (alias " ^ a ^ ")" | None -> ""));
              (match Stdlib.List.find_opt (fun g -> g.name = name) all_groups with
              | None ->
                  print_error "config" ("Local dependency not found: " ^ name);
                  Abort
              | Some dep_group ->
                  dbg ("Config.load': loading dependency group " ^ dep_group.name);
                  let _ = load' ~all_groups dep_group in
                  let ns_name = Stdlib.Option.value alias ~default:name in
                  if ns_name <> dep_group.name then begin
                    (* Create an alias struct with copied components *)
                    match Names.structLookupIn (group_ns, Names.Qid ([], dep_group.name)) with
                    | None -> Ok
                    | Some mid_dep ->
                        let alias_ns = Names.newNamespace () in
                        let comps = Names.getComponents mid_dep in
                        Names.appConsts (fun (_, cid) -> Names.insertConst (alias_ns, cid)) comps;
                        Names.appStructs (fun (_, m) -> Names.insertStruct (alias_ns, m)) comps;
                        let mid_alias = Intsyn.IntSyn.sgnStructAdd
                            (Intsyn.IntSyn.StrDec (ns_name, None)) in
                        Names.installStructName mid_alias;
                        Names.insertStruct (group_ns, mid_alias);
                        Names.installComponents (mid_alias, alias_ns);
                        Ok
                  end else Ok)
          | Local { name; alias; path = Some p } ->
              dbg ("Config.load': dependency " ^ name ^ " at " ^ Fpath.to_string p
                ^ (match alias with Some a -> " (alias " ^ a ^ ")" | None -> ""));
              (match Bos.OS.File.read p with
              | Error (`Msg msg) ->
                  print_error "config" ("Failed to read dependency file: " ^ msg); Abort
              | Ok str ->
                  (match !try_toml_ref p str with
                  | None ->
                      print_error "config" ("Not a valid TOML config: " ^ Fpath.to_string p); Abort
                  | Some sub_file ->
                      let groups = sub_file.Project.Format.groups in
                      (match Stdlib.List.find_opt (fun g -> g.Project.Format.name = name) groups with
                      | None ->
                          print_error "config"
                            ("Group '" ^ name ^ "' not found in " ^ Fpath.to_string p); Abort
                      | Some dep_group ->
                          let _ = load' ~all_groups:groups dep_group in
                          let ns_name = Stdlib.Option.value alias ~default:name in
                          if ns_name <> dep_group.Project.Format.name then
                            match Names.structLookupIn (group_ns, Names.Qid ([], dep_group.Project.Format.name)) with
                            | None -> Ok
                            | Some mid_dep ->
                                let alias_ns = Names.newNamespace () in
                                let comps = Names.getComponents mid_dep in
                                Names.appConsts (fun (_, cid) -> Names.insertConst (alias_ns, cid)) comps;
                                Names.appStructs (fun (_, m) -> Names.insertStruct (alias_ns, m)) comps;
                                let mid_alias = Intsyn.IntSyn.sgnStructAdd
                                    (Intsyn.IntSyn.StrDec (ns_name, None)) in
                                Names.installStructName mid_alias;
                                Names.insertStruct (group_ns, mid_alias);
                                Names.installComponents (mid_alias, alias_ns);
                                Ok
                          else Ok)))
          | Installed { name; _ } ->
              dbg ("Config.load': installed dependency " ^ name);
              Ok
          | External _ ->
              dbg "Config.load': external dependency (skipped)";
              Ok
        in
        let dep_results = List.map install_dep cfg.deps in
        let dep_ok = not (List.exists (fun s -> s = Abort) dep_results) in
        let main_status =
          if dep_ok then begin
            dbg ("Config.load': loading main " ^ Fpath.to_string cfg.main);
            load group_ns (File cfg.main)
          end else Abort
        in
        let mid = Intsyn.IntSyn.sgnStructAdd
            (Intsyn.IntSyn.StrDec (cfg.name, None)) in
        Names.installStructName mid;
        Names.insertStruct (saved_group_ns, mid);
        Names.installComponents (mid, group_ns);
        current_group_ns := saved_group_ns;
        current_load_path := saved_load_path;
        main_status

      let load (cfg : t) : status =
        let groups = cfg.Project.Format.groups in
        dbg ("Config.load: " ^ string_of_int (Stdlib.List.length groups) ^ " group(s)");
        let results = List.map (load' ~all_groups:groups) groups in
        if List.exists (fun s -> s = Abort) results then Abort else Ok

  end

  let () = try_toml_ref := Config.try_toml
  let () = load_toml_ref := Config.load

  let make (src : source) : status =
    dbg (match src with
       | File p -> "make: loading " ^ Fpath.to_string p
       | Input _ -> "make: loading from input");
    load (Names.newNamespace ()) src

  (* ------------------------------------------------------------------ *)
  (* Print settings                                                       *)
  (* ------------------------------------------------------------------ *)

  module Print = struct
    let implicit = Print.Print_.implicit
    let print_infix = Print.Print_.printInfix
    let depth = Print.Print_.printDepth
    let length = Print.Print_.printLength
    let indent = Print.Print_.Formatter.indent
    let width = Print.Print_.Formatter.pagewidth
    let no_shadow = Print.Print_.noShadow
    let sgn () = Print.Print_.printSgn ()
    let prog () = Print.Print_.ClausePrint.printSgn ()
    let subord () = Subordinate.Subordinate_.Subordinate.show ()
    let def () = Subordinate.Subordinate_.Subordinate.showDef ()
    let domains () = msg (Frontend.Version.Version.version_string ^ "\n")

    module Tex = struct
      let sgn () =
        msg "\\begin{bigcode}\n";
        Print.Print_.PrintTeX.printSgn ();
        msg "\\end{bigcode}\n"

      let prog () =
        msg "\\begin{bigcode}\n";
        Print.Print_.ClausePrintTeX.printSgn ();
        msg "\\end{bigcode}\n"
    end
  end

  (* ------------------------------------------------------------------ *)
  (* Reconstruction trace options                                          *)
  (* ------------------------------------------------------------------ *)

  module ReconOpts = struct
    type trace_mode = Progressive | Omniscient

    let trace = Recon.ReconTerm.trace
    let trace_mode : trace_mode ref = ref Progressive
  end

  (* ------------------------------------------------------------------ *)
  (* Execution trace settings                                             *)
  (* ------------------------------------------------------------------ *)

  module Trace = struct
    type 'a spec = None | Some of 'a list | All

    let to_opsem : string spec -> string Opsem.Opsem_.Trace.spec = function
      | None -> Opsem.Opsem_.Trace.None
      | Some lst -> Opsem.Opsem_.Trace.Some lst
      | All -> Opsem.Opsem_.Trace.All

    let trace spec = Opsem.Opsem_.Trace.trace (to_opsem spec)
    let break spec = Opsem.Opsem_.Trace.break (to_opsem spec)
    let detail = Opsem.Opsem_.Trace.detail
    let show () = Opsem.Opsem_.Trace.show ()
    let reset () = Opsem.Opsem_.Trace.reset ()
  end

  (* ------------------------------------------------------------------ *)
  (* Timers                                                               *)
  (* ------------------------------------------------------------------ *)

  module Timers = struct
    let show () = Timing.Timers.Timers.show ()
    let reset () = Timing.Timers.Timers.reset ()
    let check () = Timing.Timers.Timers.check ()
  end

  (* ------------------------------------------------------------------ *)
  (* Compiler / optimisation settings                                     *)
  (* ------------------------------------------------------------------ *)

  module Compile = struct
    type opt = No | Linear_heads | Indexing

    let optimize : opt ref = ref Linear_heads
  end

  (* ------------------------------------------------------------------ *)
  (* Meta-theorem prover settings                                         *)
  (* ------------------------------------------------------------------ *)

  module Prover = struct
    type strategy = Rfs | Frs

    let strategy : strategy ref = ref Frs
    let max_split = M2.MetaGlobal.MetaGlobal.maxSplit
    let max_recurse = M2.MetaGlobal.MetaGlobal.maxRecurse
  end

  (* ------------------------------------------------------------------ *)
  (* Tabling settings                                                     *)
  (* ------------------------------------------------------------------ *)

  module Table = struct
    type strategy = Variant | Subsumption

    let strategy : strategy ref = ref Variant
    let strengthen = Opsem.TableParam.TableParam.strengthen
    let reset_global_table = Opsem.TableParam.TableParam.resetGlobalTable
    let top () = ()
  end

  (* ------------------------------------------------------------------ *)
  (* OS utilities                                                         *)
  (* ------------------------------------------------------------------ *)

  module OS = struct
    let chdir = BasisOS.FileSys.chDir
    let getdir = BasisOS.FileSys.getDir
    let exit () = BasisOS.Process.exit BasisOS.Process.success
  end

  (* ------------------------------------------------------------------ *)
  (* Interactive evaluation                                               *)
  (* ------------------------------------------------------------------ *)

  module Eval = struct
    let eval (cmd : Cst.cmd) : unit =
      Install.install1 (Names.newNamespace ()) cmd
  end

  (* ------------------------------------------------------------------ *)
  (* Version string                                                       *)
  (* ------------------------------------------------------------------ *)

  let version : string = Frontend.Version.Version.version_string
  let top _ = assert false
  let run _ = assert false
end
