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

  let current_load_path : Fpath.t list ref =
    ref [ Result.get_ok @@ Bos.OS.Dir.current () ]

  let load_paths : (Fpath.t * string) list ref = ref []

  (* Save Basis's OS before any module definitions shadow it *)
  module BasisOS = OS
  (** Additional directories to search for included files. *)

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
  (* descriptive errors.  install1 bypasses them with failwith'.           *)
  module Recon = Recon.Make_Recon (struct
    module Paths = Paths
    module Cst = Cst
    module Syntax = Syntax
    module Ast = Intsyn.IntSyn
  end)

  (* ------------------------------------------------------------------ *)
  (* Source and mode                                                       *)
  (* ------------------------------------------------------------------ *)

  type source = Loader.source = File of Fpath.t | Input of string

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

  type status = Loader.status = Ok | Abort

  let status_to_exit = function Ok -> 0 | Abort -> 1

  (* Top-level namespace for the group currently being loaded.
     %require deposits here, escaping any inner %scope. Aliased (not
     copied) to Names.currentGroupNamespace, since %abs's resolution
     (Names.resolveQid) needs to see this namespace's live contents from
     within Names/Recon, which cannot depend on Impl. *)
  let current_group_ns : Names.namespace ref = Names.currentGroupNamespace

  (* Canonical paths already run via %require; skip on repeat (#once). *)
  let required_files : (string, unit) Hashtbl.t = Hashtbl.create 16

  (* Forward reference set after `load` is defined, breaking the cycle
     between Install.install1 (needs to call load for %require) and load
     (which calls Install.install). *)
  let load_file_ref : (Names.namespace -> Fpath.t -> Reply.outcome) ref =
    ref (fun _ns _path -> Reply.ok [])

  (* Forward reference for TOML config detection, set after Config is defined.
     load calls this to check if a file is a valid TOML project before
     treating it as source. *)
  let try_toml_ref : (Fpath.t -> string -> Project.Format.file option) ref =
    ref (fun _path _str -> None)

  let load_toml_ref : (Project.Format.file -> Reply.outcome) ref =
    ref (fun _cfg -> Reply.ok [])

  (* Forward reference for %require dispatch; set after Loader is instantiated
     below. install1 is defined before the Loader, so it calls through this ref. *)
  let handle_require_ref : (string list -> Reply.t list) ref =
    ref (fun _ids -> [])

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
    Display.message ~level:Display.Level.normal ~kind:Display.Response
      (Display.Form.string m)

  let dbg m =
    Display.message ~level:Display.Level.verbose ~kind:Display.Debug
      (Display.Form.string m)

  let print_error (label : string) (detail : string) : unit =
    Display.message ~level:Display.Level.normal ~kind:Display.Error
      (Display.Form.string (label ^ ": " ^ detail))

  let failwith' l =
    print_error "Fatal error" l;
    failwith l

  (* ------------------------------------------------------------------ *)
  (* ConDec installation                                                   *)
  (* ------------------------------------------------------------------ *)

  (* Declarations always become globally bare-visible when installed (needed
     so sibling declarations within the same %scope session, e.g. a case
     referring back to the judgment it's a case of, can see each other
     unqualified). When [scope_installs] is given (i.e. we're inside a
     %scope body), the cid is also recorded there so Cst.Scope_ can retract
     just these bindings via [Names.uninstallConst] once the session closes,
     instead of leaving them permanently global -- and struct-member
     installation becomes shadow-tolerant rather than fatal, since a
     judgment's later case clause is allowed to reuse an earlier clause's
     label (see Cst.Scope_ below). *)
  let install_condec
      ?(scope_installs : Intsyn.IntSyn.cid list ref option = None) ns
      (cd : Intsyn.IntSyn.conDec) : Intsyn.IntSyn.cid =
    let open Intsyn.IntSyn in
    let cid = sgnAdd cd in
    Names.installConstName cid;
    (match scope_installs with
    | Some acc ->
        acc := cid :: !acc;
        Names.insertConstShadow (ns, cid)
    | None -> Names.insertConst (ns, cid));
    (match cd with
    | BlockDec _ -> Subordinate.Subordinate_.Subordinate.installBlock cid
    | BlockDef _ -> ()
    | _ ->
        Index.Index_.Index.install Ordinary (Const cid);
        Compile.Compile_.Compile.install Ordinary cid;
        Subordinate.Subordinate_.Subordinate.install cid;
        Subordinate.Subordinate_.Subordinate.installDef cid);
    cid

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

  (* Build a sort's kind from its argument decls.  [%sort NAME A B C] and
     [%sort NAME {x T} (f x)] both work: a NAMED argument ([{x T}]) becomes a
     dependent [Pi] (so later arguments may refer to [x]), while an ANONYMOUS
     argument (bare [A] or [{_ A}], i.e. name [None]) becomes a non-dependent
     [Arrow].  Emitting a [Pi] for anonymous arguments would scope them over the
     rest of the kind and spuriously raise the implicit variables of later
     arguments (a higher-order [_?n]), which then derails mode and coverage
     checking.  This matches Twelf's [a -> b -> type] reconstruction. *)
  let rec factor_sort : Cst.decl list -> Cst.term = function
    | [] -> Cst.Term.typ ()
    | decl :: decls -> (
        let rest = factor_sort decls in
        match Cst.View.Decl.view decl with
        | Cst.View.Decl.Decl1 (_, [ None ], typ, _)
        | Cst.View.Decl.Decl0 (_, [ None ], typ) ->
            Cst.Term.Sugar.arrow typ rest
        | _ -> Cst.Term.pi [ decl ] rest)

  module Install = struct
    (* The %scope session currently bare-visible, if any: a name and the
       cids installed under it. A %scope NAME reopens this session when NAME
       matches (accumulating into the same struct without re-raising on a
       reused case label); a %scope with a *different* name closes it first.
       See Cst.Scope_ below. *)
    let open_scope : (string * Intsyn.IntSyn.cid list ref) option ref = ref None

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
          failwith'
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
        | s -> failwith' ("%reduces: unknown predicate " ^ s)
      in
      let term_to_order tm = TS.Varg [ term_to_head tm ] in
      let o_out, o_in, body_rest =
        match body with
        | out_tm :: in_tm :: rest ->
            (term_to_order out_tm, term_to_order in_tm, rest)
        | _ ->
            failwith'
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
              failwith'
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
              failwith'
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
      | Cst.Arrow_ (l, _, _)
      | Cst.Pi_ (l, _, _)
      | Cst.Lam_ (l, _, _)
      | Cst.App_ (l, _, _)
      | Cst.Hastype_ (l, _, _)
      | Cst.Omitted_ l
      | Cst.Typ_ l
      | Cst.MacroParam_ (l, _, _)
      | Cst.Local_ (l, _, _)
      | Cst.Foreign_ (l, _)
      | Cst.Internal_ (l, _, _) ->
          l
      | Cst.Lcid_ (_, _, l)
      | Cst.Ucid_ (_, _, l)
      | Cst.Scon_ (_, l)
      | Cst.Evar_ (_, l)
      | Cst.Fvar_ (_, l) ->
          l
      | Cst.Quid_ (_, _, _, l) -> l

    (* Returns the number of solutions found.  Solution terms themselves are
       still rendered here through the Display bus; extracting them as values
       requires a solution-callback API (phase 3). *)
    let run_query loc q : int =
      let v_, opt_name, xs_ = Recon.ReconQuery.queryToQuery (q, loc) in
      let g = Compile.Compile_.Compile.compileGoal (Intsyn.IntSyn.Null, v_) in
      let solutions = ref 0 in
      let exception Done in
      let sc m_ =
        incr solutions;
        if !Global.Global_.Global.chatter >= 3 then begin
          msg (Printf.sprintf "---------- Solution %d ----------\n" !solutions);
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
        msg "No solution.\n";
      !solutions

    let install_worlds_cmd ids tms =
      let resolve_block id =
        match Names.constLookup (Names.Qid ([], id)) with
        | None ->
            failwith' ("Undeclared block label " ^ id ^ " in worlds declaration")
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
        | Cst.View.Term.Qualified (_, (ns, n), form) ->
            Names.resolveQid ~shortest:(form = Cst.Abs) (Names.Qid (ns, n))
        | _ -> None
      in
      let resolve_family tm =
        let family_cid_opt =
          match Cst.View.Term.view tm with
          | Cst.View.Term.App (_, head, _) -> lookup_head head
          | v -> lookup_head (Cst.View.Term.review v)
        in
        match family_cid_opt with
        | None -> failwith' "%worlds: expected a type family name"
        | Some a -> a
      in
      let families = List.map resolve_family tms in
      List.app (fun a -> WorldSyn.install (a, w_)) families;
      List.app (fun a -> WorldSyn.worldcheck w_ a) families

    let install_condec_cmd ?(inline = false)
        ?(scope_installs : Intsyn.IntSyn.cid list ref option = None) ns condec
        loc : Intsyn.IntSyn.cid option =
      match Recon.ReconConDec.condecToConDec (condec, loc, inline) with
      | Some cd, _ -> Some (install_condec ~scope_installs ns cd)
      | None, _ -> None

    let name_to_cid ns label id =
      match Names.constLookupIn (ns, Names.Qid ([], id)) with
      | None ->
          failwith'
            ("Undeclared identifier " ^ id ^ " in " ^ label ^ " declaration")
      | Some cid -> cid

    (* Run [f] over [xs] in order, concatenating replies, stopping early if a
       command asks to quit (preserves the pre-refactor semantics of %quit
       aborting the rest of a file). *)
    let rec run_until_quit (f : 'a -> Reply.t list) : 'a list -> Reply.t list =
      function
      | [] -> []
      | x :: rest ->
          let rs = f x in
          if Reply.quit_requested rs then rs else rs @ run_until_quit f rest

    let installed = function [] -> [] | cids -> [ Reply.Installed cids ]

    let rec install1 ?(path = None)
        ?(scope_installs : Intsyn.IntSyn.cid list ref option = None) ns
        (cmd : Cst.cmd) : Reply.t list =
      let filename =
        Stdlib.Option.value
          (Option.map Fpath.to_string path)
          ~default:"<INTERACTIVE>"
      in
      Debug.(
        msg' ~src:Group.pal ~level:Level.Debug Fmt.string "Installing command");
      (* A %scope session (see Cst.Scope_ below) stays bare-visible across
         multiple %scope NAME commands, but must not leak into whatever
         top-level command comes next once the caller has moved on from NAME
         -- otherwise a %scope-declared name (e.g. a case label that happens
         to collide with an unrelated bare declaration's name elsewhere in
         the file, like "s") stays shadowed forever. [scope_installs = None]
         means we're not currently inside a %scope body's own recursive
         install1 call, so this is exactly the top-level boundary where a
         still-open session from an *earlier* command must be closed unless
         the command about to run is a %scope reopening of the same name. *)
      (match (scope_installs, !open_scope, cmd) with
      | None, Some (cur_name, _), Cst.Scope_ (name, _) when cur_name = name ->
          ()
      | None, Some (_, cur_installs), _ ->
          List.app Names.uninstallConst !cur_installs;
          open_scope := None
      | _ -> ());
      match cmd with
      | Cst.SortCmd_ (ids, decls) ->
          let sort_loc =
            match decls with d :: _ -> decl_loc d | [] -> Cst.ghost
          in
          installed
            (Stdlib.List.filter_map
               (fun id ->
                 Debug.(
                   msg' ~src:Group.pal ~level:Level.Debug
                     Fmt.(const string "Installing sort" ++ sp ++ string)
                     id);
                 let kind = factor_sort decls in
                 let name_opt = if id = "_" then None else Some id in
                 let condec =
                   Cst.ConDec.constant_decl (Cst.Decl.decl1 [ name_opt ] kind)
                 in
                 install_condec_cmd ~scope_installs ns condec
                   (loc_of filename sort_loc))
               ids)
      | Cst.TermCmd_ decl ->
          Debug.(
            msg' ~src:Group.pal ~level:Level.Debug Fmt.string
              "Installing term command");

          let names, ty =
            match Cst.View.Decl.view decl with
            | Cst.View.Decl.Decl1 (_, ns, t, _) -> (ns, t)
            | Cst.View.Decl.Decl0 (_, ns, t) -> (ns, t)
          in
          let names' = List.map (function Some n -> n | None -> "_") names in
          Display.message ~level:Display.Level.verbose
            Display.(
              string "Installing term command for"
              ++ each string names' ++ space ()
              ++ hvbox [ shown Cst.show_term ty ]);
          let term_loc = loc_of filename (decl_loc decl) in
          installed
            (Stdlib.List.filter_map
               (fun name_opt ->
                 let condec =
                   Cst.ConDec.constant_decl (Cst.Decl.decl1 [ name_opt ] ty)
                 in
                 install_condec_cmd ~scope_installs ns condec term_loc)
               names)
      | Cst.DefineCmd_ (Cst.Define_ (name_opt, tm, tp_opt)) ->
          let name = match name_opt with Some n -> n | None -> "_" in
          let condec = Cst.ConstantDef_ (name, tm, tp_opt) in
          installed
            (Stdlib.Option.to_list
               (install_condec_cmd ~scope_installs ns condec
                  (loc_of filename (term_loc tm))))
      | Cst.QueryCmd_ (_n, _b, _d, (Cst.Query_ (_, qtm) as q)) ->
          [ Reply.Solutions (run_query (loc_of filename (term_loc qtm)) q) ]
      | Cst.SolveCmd_ (Cst.Solve_ (_, stm) as sol) ->
          let v_, sc_fn =
            Recon.ReconQuery.solveToSolve
              ([], sol, loc_of filename (term_loc stm))
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
            | None -> failwith' "%solve: no solution found"
            | Some m_ -> m_
          in
          installed
            (Stdlib.List.map
               (fun (cd, _) -> install_condec ~scope_installs ns cd)
               (sc_fn m_))
      | Cst.StopCmd_ -> []
      | Cst.QuitCmd_ -> [ Reply.Quit ]
      | Cst.HelpCmd_ topic ->
          begin match topic with
          | None ->
              [
                Reply.Response
                  "Commands: sort, term, query, define, solve, quit, help, \
                   get, set, version\n";
              ]
          | Some t ->
              [ Reply.Response (("No help available for '" ^ t) ^ "'\n") ]
          end
      | Cst.GetCmd_ key ->
          begin match Options.get key with
          | Some v -> [ Reply.Response ((key ^ " = ") ^ v ^ "\n") ]
          | None -> [ Reply.Response (key ^ " is not set\n") ]
          end
      | Cst.SetCmd_ (key, value) ->
          Options.set key value;
          []
      | Cst.VersionCmd_ ->
          [ Reply.Response (Frontend.Version.Version.version_string ^ "\n") ]
      | Cst.EvalCmd_ cmds ->
          run_until_quit (install1 ~path ~scope_installs ns) cmds
      | Cst.AdhocQueryCmd_ (Cst.Query_ (_, qtm) as q) ->
          [ Reply.Solutions (run_query (loc_of filename (term_loc qtm)) q) ]
      | Cst.DeclCmd_ tm ->
          let qid_opt =
            match Cst.View.Term.view tm with
            | Cst.View.Term.Lowercase (_, (ns, n)) ->
                Some (Names.Qid (ns, n), false)
            | Cst.View.Term.Uppercase (_, (ns, n)) ->
                Some (Names.Qid (ns, n), false)
            | Cst.View.Term.Qualified (_, (ns, n), form) ->
                Some (Names.Qid (ns, n), form = Cst.Abs)
            | _ -> None
          in
          begin match qid_opt with
          | None -> [ Reply.Response "decl: expected an identifier\n" ]
          | Some (qid, shortest) ->
              begin match Names.resolveQid ~shortest qid with
              | None ->
                  [
                    Reply.Response
                      (Names.qidToString qid ^ " has not been declared\n");
                  ]
              | Some cid -> [ Reply.Decl (Intsyn.IntSyn.sgnLookup cid) ]
              end
          end
      | Cst.FreezeCmd_ ids ->
          let cids = List.map (name_to_cid ns "freeze") ids in
          ignore (Subordinate.Subordinate_.Subordinate.freeze cids);
          []
      | Cst.ThawCmd_ ids ->
          if not !unsafe then failwith' "%thaw not safe: Toggle `unsafe' flag";
          let cids = List.map (name_to_cid ns "thaw") ids in
          ignore (Subordinate.Subordinate_.Subordinate.thaw cids);
          []
      | Cst.DeterministicCmd_ ids ->
          let cids = List.map (name_to_cid ns "deterministic") ids in
          List.app
            (fun cid -> Compile.CompSyn.CompSyn.detTableInsert (cid, true))
            cids;
          []
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
            ids;
          []
      | Cst.SymbolCmd_ (pref, id) ->
          let cid = name_to_cid ns "symbol" id in
          Names.installAlias (pref, cid);
          Names.insertConstAlias (ns, pref, cid);
          Names.installNamePref (cid, ([ pref ], [ pref ]));
          []
      | Cst.InlineCmd_ (name, tm) ->
          let condec = Cst.ConstantDef_ (name, tm, None) in
          installed
            (Stdlib.Option.to_list
               (install_condec_cmd ~inline:true ~scope_installs ns condec
                  (loc_of filename (term_loc tm))))
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
          let condec = Cst.BlockDecl_ (id, somes, pis) in
          installed
            (Stdlib.Option.to_list
               (install_condec_cmd ~scope_installs ns condec
                  (loc_of filename block_loc)))
      | Cst.ModeCmd_ md ->
          let () =
            Display.(
              message ~level:Level.verbose
                (string "Installing mode declaration for "
                ++ shown Cst.show_modeDec md))
          in
          let mdec, _r = Recon.ReconMode.modeToMode md in
          let cid, _ = mdec in
          (match ModeTable.modeLookup cid with
          | Some _ when Subordinate.Subordinate_.Subordinate.frozen [ cid ] ->
              failwith'
                ("Cannot redeclare mode for frozen constant "
                ^ Names.qidToString (Names.constQid cid))
          | _ -> ());
          ModeTable.installMode mdec;
          ModeCheck.checkMode mdec;
          []
      | Cst.TotalCmd_ (intros, body) ->
          let t_, rrs = build_thm_tdecl "%total" intros body in
          let la_ = ThmInst.installTotal (t_, rrs) in
          List.app ThmTotal.install la_;
          List.app ThmTotal.checkFam la_;
          []
      | Cst.TerminatesCmd_ (intros, body) ->
          let t_, rrs = build_thm_tdecl "%terminates" intros body in
          let la_ = ThmInst.installTerminates (t_, rrs) in
          ignore la_;
          []
      | Cst.CoversCmd_ md ->
          let mdec, _r = Recon.ReconMode.modeToMode md in
          Cover.checkCovers mdec;
          []
      | Cst.NameCmd_ _id -> []
      | Cst.ProseCmd_ _id -> []
      | Cst.ReducesCmd_ (pred_str, body) ->
          let r_, rrs = build_thm_rdecl pred_str body in
          let la_ = ThmInst.installReduces (r_, rrs) in
          List.app Terminate.Terminate_.Reduces.checkFamReduction la_;
          []
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
          | None -> [ Reply.Response "unique: expected a type family name\n" ]
          | Some ((cid, _) as mdec) ->
              UniqueTable.installMode mdec;
              Unique.checkUnique mdec;
              []
          end
      | Cst.UnionCmd_ (id, ids) ->
          let syms = List.map (fun s -> ([], s)) ids in
          let condec = Cst.BlockDef_ (id, syms) in
          installed
            (Stdlib.Option.to_list
               (install_condec_cmd ~scope_installs ns condec
                  (loc_of filename Cst.ghost)))
      | Cst.WorldsCmd_ (ids, tms) ->
          install_worlds_cmd ids tms;
          []
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
          if !solutions = 0 && !chatter >= 3 then msg "No tabled solution.\n";
          [ Reply.Solutions !solutions ]
      | Cst.Open_ ids ->
          let qid =
            match List.rev ids with
            | [] -> failwith' "%open: empty module path"
            | last :: prefix -> Names.Qid (List.rev prefix, last)
          in
          let mid =
            match Names.structLookupIn (ns, qid) with
            | Some m -> m
            | None -> (
                match Names.structLookup qid with
                | Some m -> m
                | None ->
                    failwith' ("%open: unknown module " ^ Names.qidToString qid)
                )
          in
          let comps = Names.getComponents mid in
          (* %open promotes a structure's members to unqualified visibility,
             matching the reference SML Twelf's %open
             (twelf/src/modules/modsyn.fun): install their bare names
             globally (not just into the qualified-lookup table [ns]), so a
             plain %scope no longer does this by itself (see Cst.Scope_
             below) -- %open is what actually makes it happen. If this %open
             itself runs inside an enclosing %scope body, [scope_installs]
             is Some, and the promotion is recorded so it gets retracted
             along with the rest of that body's declarations when the
             enclosing scope closes, same as a %open at the true top level
             (scope_installs = None) staying permanent. *)
          Names.appConsts
            (fun (_, cid) ->
              Names.installConstName cid;
              (match scope_installs with
              | Some acc -> acc := cid :: !acc
              | None -> ());
              Names.insertConst (ns, cid))
            comps;
          Names.appStructs (fun (_, m) -> Names.insertStruct (ns, m)) comps;
          []
      | Cst.Scope_ (name, body_cmd) ->
          (* A `%scope NAME` naming NAME already in [ns] reopens that
             structure (the corpus idiom is one `%scope NAME %term case ...`
             per clause, expecting all clauses -- possibly separated by other,
             unrelated commands -- to accumulate into the same structure)
             rather than declaring a fresh, colliding one. *)
          let mid, child_ns =
            match Names.structLookupIn (ns, Names.Qid ([], name)) with
            | Some mid -> (mid, Names.getComponents mid)
            | None ->
                let child_ns = Names.newNamespace () in
                let mid =
                  Intsyn.IntSyn.sgnStructAdd (Intsyn.IntSyn.StrDec (name, None))
                in
                Names.installStructName mid;
                Names.insertStruct (ns, mid);
                (mid, child_ns)
          in
          (* A %scope session stays open (bare-visible) across multiple
             %scope NAME commands as long as NAME keeps matching -- so a
             judgment's clauses can be interleaved with unrelated commands
             and still see each other/reuse case labels like "pi1" for both
             an inductive and a "closed" sub-case. Closing on any other
             command (a different-named %scope, or a return to bare
             top-level declarations) is handled uniformly by the check at
             the top of [install1], so by the time we reach here [open_scope]
             is already either [None] or [Some (name, _)]. *)
          let body_installs =
            match !open_scope with
            | Some (cur_name, cur_installs) when cur_name = name -> cur_installs
            | _ ->
                let installs = ref [] in
                Names.appConsts
                  (fun (_, cid) ->
                    Names.installConstName cid;
                    installs := cid :: !installs)
                  child_ns;
                open_scope := Some (name, installs);
                installs
          in
          let rs =
            install1 ~path ~scope_installs:(Some body_installs) child_ns
              body_cmd
          in
          Names.installComponents (mid, child_ns);
          rs
      | Cst.Use_ _ ->
          failwith'
            "%use: module instantiation not yet implemented in this frontend"
      | Cst.Macro_ _ -> failwith' "Macros not yet implemented in this frontend"
      | Cst.Seq_ cmds ->
          run_until_quit (install1_item ~path ~scope_installs ns) cmds
      | Cst.Require_ ids -> !handle_require_ref ids

    and install1_item ?(path = None)
        ?(scope_installs : Intsyn.IntSyn.cid list ref option = None) ns
        (item : Cst.item) : Reply.t list =
      match item with
      | Cst.Outer _ -> []
      | Cst.Cmd cmd -> install1 ~path ~scope_installs ns cmd

    let install ?(path = None) ns (cmds : Cst.cmd list) : Reply.t list =
      run_until_quit (install1 ~path ns) cmds

    let reset () : unit =
      open_scope := None;
      current_group_ns := Names.newNamespace ();
      Hashtbl.reset required_files;
      Hashtbl.reset Options.tbl;
      Frontend.Frontend_.Stelf.reset ()
  end

  (* ------------------------------------------------------------------ *)
  (* Loading                                                              *)
  (* ------------------------------------------------------------------ *)

  (* Message for a truly unrecognized exception (e.g. [Subscript],
     [Not_found]) caught by a catch-all handler: its string form carries no
     explanatory message, so when running verbose or above we append the
     captured backtrace to make these otherwise-opaque crashes diagnosable.
     Backtrace recording is enabled in [Smlofnj].  Call this FIRST in a
     handler, before any further raise, so [get_backtrace] reads the trace of
     the exception just caught. *)
  let unknown_exn_message exn =
    let base = Printexc.to_string exn in
    if Display.Info.from_chatter !chatter >= Display.Info.Level.verbose then
      match Printexc.get_backtrace () with "" -> base | bt -> base ^ "\n" ^ bt
    else base

  let load_string ?(path = None) ?(ns_init = None) (str : string) :
      Reply.outcome =
    dbg ("load_string: " ^ source_to_string path);
    let ns =
      match ns_init with Some r -> r | None -> ref (Names.newNamespace ())
    in
    let loc = Cst.ghost in
    try
      let cmds = ModernImpl.run (Cmd.parse ()) ns loc str in
      try Reply.ok (Install.install ~path !ns cmds) with
      | Error.Error.Err _ as e -> raise e
      | Recon.ReconConDec.Error msg
      | Recon.ReconTerm.Error msg
      | Recon.ReconModule.Error msg
      | Recon.ReconQuery.Error msg ->
          Error.Error.err ~stage:Error.Error.Recon (Display.Form.string msg)
      | Recon.ReconMode.Error msg | Recon.ReconThm.Error msg ->
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
            (Display.Form.string (unknown_exn_message exn))
    with
    | Error.Error.Err (stage, form) ->
        Reply.fail { Reply.stage; message = form }
    | Modern.Modern.ParseError e ->
        (* Fallback during transition; should no longer be reached *)
        Reply.fail
          {
            Reply.stage = Error.Error.Parse;
            message =
              Display.Form.string (source_to_string path ^ ": parse error: " ^ e);
          }
    | exn ->
        Reply.fail
          {
            Reply.stage = Error.Error.Unknown;
            message = Display.Form.string (unknown_exn_message exn);
          }

  let load ns (src : source) : Reply.outcome =
    let ns_ref = ref ns in
    match src with
    | Input str ->
        dbg "load: loading from input";
        load_string ~ns_init:(Some ns_ref) str
    | File path -> (
        dbg ("load: loading file " ^ Fpath.to_string path);
        let filename = Some path in
        match Bos.OS.File.read path with
        | Error (`Msg msg) ->
            Reply.fail
              {
                Reply.stage = Error.Error.Other "io";
                message = Display.Form.string ("Failed to read file: " ^ msg);
              }
        | Ok str -> (
            try
              match !try_toml_ref path str with
              | Some cfg ->
                  dbg ("load: detected TOML config in " ^ Fpath.to_string path);
                  !load_toml_ref cfg
              | None ->
                  let saved_load_path = !current_load_path in
                  let parent = Fpath.parent path in
                  current_load_path := parent :: !current_load_path;
                  let result =
                    load_string ~path:filename ~ns_init:(Some ns_ref) str
                  in
                  current_load_path := saved_load_path;
                  result
            with exn ->
              Reply.fail
                {
                  Reply.stage = Error.Error.Unknown;
                  message = Display.Form.string (unknown_exn_message exn);
                }))

  let () = load_file_ref := fun ns fp -> load ns (File fp)

  module Loader = Loader.Make (struct
    module Names = Names

    let current_load_path = current_load_path
    let current_group_ns = current_group_ns
    let required_files = required_files
    let load_file_ref = load_file_ref
    let try_toml_ref = try_toml_ref
    let dbg = dbg
    let print_error = print_error
  end)

  module Config = Loader.Config

  let () = handle_require_ref := Loader.handle_require
  let () = try_toml_ref := Config.try_toml
  let () = load_toml_ref := Config.load

  let read_decl () : Reply.outcome =
    begin match TextIO.inputLine TextIO.stdIn with
    | Some line -> load_string ~path:None line
    | None -> Reply.ok []
    end

  let decl (name : string) : Reply.outcome =
    begin match Names.stringToQid name with
    | None ->
        Reply.fail
          {
            Reply.stage = Error.Error.Other "decl";
            message =
              Display.Form.string (name ^ " is not a valid qualified identifier");
          }
    | Some qid ->
        begin match Names.constLookup qid with
        | None ->
            Reply.fail
              {
                Reply.stage = Error.Error.Other "decl";
                message = Display.Form.string (name ^ " has not been declared");
              }
        | Some cid -> Reply.ok [ Reply.Decl (Intsyn.IntSyn.sgnLookup cid) ]
        end
    end

  let make (src : source) : Reply.outcome =
    dbg
      (match src with
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
    let eval (cmd : Cst.cmd) : Reply.t list =
      Install.install1 (Names.newNamespace ()) cmd
  end

  (* ------------------------------------------------------------------ *)
  (* Version string                                                       *)
  (* ------------------------------------------------------------------ *)

  let version : string = Frontend.Version.Version.version_string
  let top _ = assert false
  let run _ = assert false
end
