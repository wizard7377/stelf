open! Basis

(** Shared result type for all loading operations. Defined here so [Impl] can
    alias it and avoid OCaml's type-alias cycle check. *)
type status = Ok | Abort

(** Input source for loading: a file path or an inline string. *)
type source = File of Fpath.t | Input of string

(** Context injected by [Impl] to break the mutual dependency between the
    loading machinery and the command installer. *)
module type CTX = sig
  module Names : Names.NAMES.NAMES

  val current_load_path : Fpath.t list ref
  val current_group_ns : Names.namespace ref
  val required_files : (string, unit) Hashtbl.t
  val load_file_ref : (Names.namespace -> Fpath.t -> Reply.outcome) ref
  val try_toml_ref : (Fpath.t -> string -> Project.Format.file option) ref
  val dbg : string -> unit
  val print_error : string -> string -> unit
end

module Make (C : CTX) = struct
  open C

  (* ------------------------------------------------------------------ *)
  (* %require handler                                                     *)
  (* ------------------------------------------------------------------ *)

  let handle_require (ids : string list) : Reply.t list =
    let rel = String.concatWith "/" ids in
    let req_path = Fpath.v rel in
    let parent_dir = Fpath.parent req_path in
    let stem = Fpath.to_string (Fpath.rem_ext (Fpath.base req_path)) in
    let is_source_ext ext = ext <> "" && ext <> ".cfg" && ext <> ".toml" in
    let found =
      Stdlib.List.find_map
        (fun base_dir ->
          let search_dir = Fpath.(base_dir // parent_dir) in
          match Bos.OS.Dir.contents search_dir with
          | Error _ -> None
          | Ok entries ->
              Stdlib.List.find_opt
                (fun entry ->
                  let b = Fpath.base entry in
                  Fpath.to_string (Fpath.rem_ext b) = stem
                  && is_source_ext (Fpath.get_ext b))
                entries)
        !current_load_path
    in
    match found with
    | None -> failwith ("%require: file not found: " ^ rel)
    | Some file_path ->
        let canon = Fpath.to_string (Fpath.normalize file_path) in
        dbg ("%%require: resolved " ^ rel ^ " -> " ^ canon);
        if not (Hashtbl.mem required_files canon) then begin
          dbg ("%%require: loading " ^ canon);
          Hashtbl.add required_files canon ();
          let o = !load_file_ref !current_group_ns file_path in
          match o.Reply.error with
          | None ->
              dbg ("%%require: finished " ^ canon);
              o.Reply.replies
          | Some e ->
              (* Propagate the nested failure with %require context attached;
                 the outermost load turns it back into a Reply.error. *)
              Error.Error.err ~stage:e.Reply.stage
                Display.Form.(
                  e.Reply.message +++ nl ()
                  +++ string
                        ("(while loading " ^ Fpath.to_string file_path
                       ^ ", required here)"))
        end
        else begin
          dbg ("%%require: skipping " ^ canon ^ " (already loaded)");
          []
        end

  (* ------------------------------------------------------------------ *)
  (* Configuration file management                                        *)
  (* ------------------------------------------------------------------ *)

  module Config = struct
    type t = Project.Format.file

    let read (src : source) : t =
      let str =
        match src with
        | Input str -> str
        | File path -> (
            try
              let ic = TextIO.openIn (Fpath.to_string path) in
              let str = TextIO.inputAll ic in
              let () = TextIO.closeIn ic in
              str
            with exn ->
              let msg =
                "Failed to read config file " ^ Fpath.to_string path ^ ": "
                ^ Printexc.to_string exn
              in
              print_error "pal" msg;
              failwith msg)
      in
      let toml =
        match Otoml.Parser.from_string str with
        | toml -> toml
        | exception Otoml.Parse_error (pos_opt, msg) ->
            let loc =
              match pos_opt with
              | Some (line, col) ->
                  Printf.sprintf " at line %d, col %d" line col
              | None -> ""
            in
            let full = Printf.sprintf "TOML parse error%s: %s" loc msg in
            print_error "pal" full;
            failwith full
        | exception exn ->
            let msg = "TOML parse error: " ^ Printexc.to_string exn in
            print_error "pal" msg;
            failwith msg
      in
      match Project.Format.from_toml toml with
      | Error msg ->
          print_error "pal" msg;
          failwith msg
      | Ok config -> config

    let rebase_group base_dir (g : Project.Format.t) : Project.Format.t =
      let open Project.Format in
      let rebase_dep = function
        | Local ({ path = Some p; _ } as d) ->
            Local { d with path = Some Fpath.(base_dir // p) }
        | dep -> dep
      in
      {
        g with
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
            let loc =
              match pos_opt with
              | Some (line, col) ->
                  Printf.sprintf " at line %d, col %d" line col
              | None -> ""
            in
            print_error "config"
              (Printf.sprintf "TOML parse error in %s%s: %s"
                 (Fpath.to_string path) loc msg)
          end;
          None
      | exception exn ->
          if is_toml then
            print_error "config"
              ("Error reading TOML config " ^ Fpath.to_string path ^ ": "
             ^ Printexc.to_string exn);
          None
      | toml -> (
          match Project.Format.from_toml toml with
          | Error msg ->
              if is_toml then
                print_error "config" (Fpath.to_string path ^ ": " ^ msg);
              None
          | Ok cfg ->
              let groups =
                List.map (rebase_group base_dir) cfg.Project.Format.groups
              in
              Some { cfg with Project.Format.groups })

    let cfg_fail (msg : string) : Reply.outcome =
      Reply.fail
        {
          Reply.stage = Error.Error.Other "config";
          message = Display.Form.string msg;
        }

    (* Combine sub-outcomes evaluated in order: replies concatenate, the
       first error wins. *)
    let combine (outcomes : Reply.outcome list) : Reply.outcome =
      let replies =
        Stdlib.List.concat_map
          (fun (o : Reply.outcome) -> o.Reply.replies)
          outcomes
      in
      let error =
        Stdlib.List.find_map (fun (o : Reply.outcome) -> o.Reply.error) outcomes
      in
      { Reply.replies; error }

    let rec load' ~(all_groups : Project.Format.t list) (cfg : Project.Format.t)
        : Reply.outcome =
      let open Project.Format in
      dbg
        ("Config.load': group " ^ cfg.name ^ ", main="
       ^ Fpath.to_string cfg.main);
      let group_ns = Names.newNamespace () in
      let saved_group_ns = !current_group_ns in
      let saved_load_path = !current_load_path in
      current_group_ns := group_ns;
      current_load_path := if cfg.dirs = [] then [ Fpath.v "." ] else cfg.dirs;
      (* Once a dependency group has loaded, expose it in this group's
         namespace under its (possibly aliased) name. *)
      let alias_dep dep_group_name alias =
        let ns_name = Stdlib.Option.value alias ~default:dep_group_name in
        if ns_name <> dep_group_name then
          match
            Names.structLookupIn (group_ns, Names.Qid ([], dep_group_name))
          with
          | None -> ()
          | Some mid_dep ->
              let alias_ns = Names.newNamespace () in
              let comps = Names.getComponents mid_dep in
              Names.appConsts
                (fun (_, cid) -> Names.insertConst (alias_ns, cid))
                comps;
              Names.appStructs
                (fun (_, m) -> Names.insertStruct (alias_ns, m))
                comps;
              let mid_alias =
                Intsyn.IntSyn.sgnStructAdd
                  (Intsyn.IntSyn.StrDec (ns_name, None))
              in
              Names.installStructName mid_alias;
              Names.insertStruct (group_ns, mid_alias);
              Names.installComponents (mid_alias, alias_ns)
      in
      let install_dep dep : Reply.outcome =
        match dep with
        | Local { name; alias; path = None } -> (
            dbg
              ("Config.load': dependency " ^ name
              ^ match alias with Some a -> " (alias " ^ a ^ ")" | None -> "");
            match Stdlib.List.find_opt (fun g -> g.name = name) all_groups with
            | None -> cfg_fail ("Local dependency not found: " ^ name)
            | Some dep_group ->
                dbg ("Config.load': loading dependency group " ^ dep_group.name);
                let o = load' ~all_groups dep_group in
                if not (Reply.failed o) then alias_dep dep_group.name alias;
                o)
        | Local { name; alias; path = Some p } -> (
            dbg
              ("Config.load': dependency " ^ name ^ " at " ^ Fpath.to_string p
              ^ match alias with Some a -> " (alias " ^ a ^ ")" | None -> "");
            match Bos.OS.File.read p with
            | Error (`Msg msg) ->
                cfg_fail ("Failed to read dependency file: " ^ msg)
            | Ok str -> (
                match !try_toml_ref p str with
                | None ->
                    cfg_fail ("Not a valid TOML config: " ^ Fpath.to_string p)
                | Some sub_file -> (
                    let groups = sub_file.Project.Format.groups in
                    match
                      Stdlib.List.find_opt
                        (fun g -> g.Project.Format.name = name)
                        groups
                    with
                    | None ->
                        cfg_fail
                          ("Group '" ^ name ^ "' not found in "
                         ^ Fpath.to_string p)
                    | Some dep_group ->
                        let o = load' ~all_groups:groups dep_group in
                        if not (Reply.failed o) then
                          alias_dep dep_group.Project.Format.name alias;
                        o)))
        | Installed { name; _ } ->
            dbg ("Config.load': installed dependency " ^ name);
            Reply.ok []
        | External _ ->
            dbg "Config.load': external dependency (skipped)";
            Reply.ok []
      in
      let deps_outcome = combine (List.map install_dep cfg.deps) in
      let main_outcome =
        if not (Reply.failed deps_outcome) then begin
          dbg ("Config.load': loading main " ^ Fpath.to_string cfg.main);
          !load_file_ref group_ns cfg.main
        end
        else Reply.ok []
      in
      let mid =
        Intsyn.IntSyn.sgnStructAdd (Intsyn.IntSyn.StrDec (cfg.name, None))
      in
      Names.installStructName mid;
      Names.insertStruct (saved_group_ns, mid);
      Names.installComponents (mid, group_ns);
      current_group_ns := saved_group_ns;
      current_load_path := saved_load_path;
      combine [ deps_outcome; main_outcome ]

    let load (cfg : t) : Reply.outcome =
      let groups = cfg.Project.Format.groups in
      dbg
        ("Config.load: "
        ^ string_of_int (Stdlib.List.length groups)
        ^ " group(s)");
      combine (List.map (load' ~all_groups:groups) groups)
  end
end
