module Format_ = struct
  type depends =
    | Local of {
        name : string; (* `[name]` *)
        alias : string option (* `[alias]` *);
        path : Fpath.t option (* `[path]` *);
      }
    | Installed of {
        name : string; (* `[name]` *)
        alias : string option (* `[alias]` *);
      }
    | External of {
        ext : ext; (* Where to find (table) `[link]` *)
        path : Fpath.t option;  (** where to put (string) `[path]` *)
        post : depends;  (** What to do after retrieved (table) *)
      }

  (** Need to load something else *)
  and ext =
    | Github of {
        user : string;  (** User key, string `[user]` *)
        repo : string;  (** Repo key, string `[repo]` *)
      }  (** Github source `[github]` (table) *)
    | Url of { url : string  (** Url *) }  (** Fetch from URL `[url]` *)

  type t = {
    name : string;  (** It has a name `[name]` (string) *)
    dirs : Fpath.t list;
        (** directories to be searched `[dirs]` (list of strings) *)
    deps : depends list;  (** dependencies `[[deps]]` (list of dependencies) *)
    main : Fpath.t;  (** Main file to load whenever used `[main]` (string) *)
  }
  (** A group (specified by `[[group]]` (can be mutiple per file), is a single
      unit *)

  type file = { groups : t list; interactive : string option }
  (** A parsed project file: [[group]] tables plus an optional top-level
      [interactive] key naming the group to load in REPL mode. *)
end

module Format : sig
  include module type of Format_

  val from_toml : Otoml.t -> (file, string) result
end = struct
  include Format_

  (* Option monad for depends/ext helpers — unknown dep types are silently skipped *)
  let ( let* ) = Option.bind

  let fpath_opt s =
    match Fpath.of_string s with Ok p -> Some p | Error _ -> None

  let rec depends_of_toml toml =
    let* type_ = Otoml.Helpers.find_string_opt toml [ "type" ] in
    match type_ with
    | "local" ->
        let* name = Otoml.Helpers.find_string_opt toml [ "name" ] in
        let alias = Otoml.Helpers.find_string_opt toml [ "alias" ] in
        let path =
          Option.bind (Otoml.Helpers.find_string_opt toml [ "path" ]) fpath_opt
        in
        Some (Local { name; alias; path })
    | "installed" ->
        let* name = Otoml.Helpers.find_string_opt toml [ "name" ] in
        let alias = Otoml.Helpers.find_string_opt toml [ "alias" ] in
        Some (Installed { name; alias })
    | "external" ->
        let* link = Otoml.find_opt toml Otoml.get_value [ "link" ] in
        let* ext = ext_of_toml link in
        let path =
          Option.bind (Otoml.Helpers.find_string_opt toml [ "path" ]) fpath_opt
        in
        let* post_t = Otoml.find_opt toml Otoml.get_value [ "post" ] in
        let* post = depends_of_toml post_t in
        Some (External { ext; path; post })
    | _ -> None

  and ext_of_toml link =
    match Otoml.find_opt link Otoml.get_value [ "github" ] with
    | Some gh ->
        let* user = Otoml.Helpers.find_string_opt gh [ "user" ] in
        let* repo = Otoml.Helpers.find_string_opt gh [ "repo" ] in
        Some (Github { user; repo })
    | None ->
        let* url = Otoml.Helpers.find_string_opt link [ "url" ] in
        Some (Url { url })

  (* Result monad for group/file parsing — missing fields are errors *)
  let ( let*! ) x f = match x with Ok v -> f v | Error _ as e -> e

  let required_string toml key =
    match Otoml.Helpers.find_string_opt toml key with
    | Some s -> Ok s
    | None ->
        Error
          (Printf.sprintf "missing required field %S" (String.concat "." key))

  let fpath_r label s =
    match Fpath.of_string s with
    | Ok p -> Ok p
    | Error (`Msg msg) ->
        Error (Printf.sprintf "invalid %s path %S: %s" label s msg)

  let group_of_toml toml =
    let*! name = required_string toml [ "name" ] in
    let*! dirs_s =
      match
        List.find_map
          (fun key -> Otoml.Helpers.find_strings_opt toml [ key ])
          [ "dirs"; "srcs"; "src"; "dir" ]
      with
      | Some ss -> Ok ss
      | None ->
          Error {|missing required field "dirs" (or "srcs" / "src" / "dir")|}
    in
    let dirs = List.filter_map fpath_opt dirs_s in
    let*! main_s = required_string toml [ "main" ] in
    let*! main = fpath_r "main" main_s in
    let deps =
      match
        List.find_map
          (fun key ->
            Otoml.find_opt toml
              (Otoml.get_array ~strict:false Otoml.get_value)
              [ key ])
          [ "deps"; "dependencies" ]
      with
      | Some items -> List.filter_map depends_of_toml items
      | None -> []
    in
    Ok { name; dirs; deps; main }

  let from_toml toml =
    let interactive = Otoml.Helpers.find_string_opt toml [ "interactive" ] in
    match
      Otoml.find_opt toml
        (Otoml.get_array ~strict:false Otoml.get_value)
        [ "group" ]
    with
    | None -> Error "missing required [[group]] section"
    | Some groups ->
        let results = List.map group_of_toml groups in
        let errors =
          List.filter_map (function Error e -> Some e | Ok _ -> None) results
        in
        if errors <> [] then Error (String.concat "; " errors)
        else
          let valid =
            List.filter_map
              (function Ok g -> Some g | Error _ -> None)
              results
          in
          Ok { groups = valid; interactive }
end
