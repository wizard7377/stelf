let ( let* ) = Result.bind

let is_invalid_char = function
  | ' ' | '\t' | '\n' | '\r' | '(' | ')' | '[' | ']' | '{' | '}' | '"' | '\\'
  | '/' ->
      true
  | _ -> false

let validate_name name : (unit, [ `Msg of string ]) result =
  if name = "" then Error (`Msg "project name must not be empty")
  else if name = "." || name = ".." then
    Error (`Msg "project name must not be \".\" or \"..\"")
  else if String.exists is_invalid_char name then
    Error
      (`Msg
         "project name must not contain whitespace, brackets, quotes, \
          backslashes, or slashes")
  else Ok ()

let run_t = {run_t|  $ stelf check stelf.toml

  $ stelf repl stelf.toml
|run_t}

let dune_file = ""
let main_lf = ""

let schema_json =
  {json|{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://stelf.dev/schemas/stelf.toml/1.0.0.json",
  "title": "stelf.toml",
  "description": "JSON Schema for STELF project files (stelf.toml), generated from stelf.tosd version 1.0.0.",
  "type": "object",
  "properties": {
    "interactive": {
      "description": "The group to load by default when opening the REPL without specifying one. If omitted, the user must name a group explicitly on the command line. Does not affect how this file behaves when used as a dependency.",
      "$ref": "#/$defs/name"
    },
    "group": {
      "description": "The list of groups defined in this file.",
      "type": "array",
      "items": { "$ref": "#/$defs/group" }
    }
  },
  "required": ["group"],
  "additionalProperties": false,

  "$defs": {
    "name": {
      "description": "A valid STELF identifier: any non-whitespace, non-bracket character sequence, with %%. as an escape prefix for special characters.",
      "type": "string",
      "pattern": "([^\\s\\(\\)\\[\\]\\{\\}]|%%.)+"
    },

    "file": {
      "description": "A path to a file.",
      "type": "string"
    },

    "dir": {
      "description": "A path to a directory.",
      "type": "string"
    },

    "url": {
      "description": "A URL string.",
      "type": "string"
    },

    "dependencyExternal": {
      "description": "An external dependency: downloaded from a URL into a local directory, then treated as a local dependency rooted at that directory.",
      "type": "object",
      "properties": {
        "url": {
          "description": "The URL to download from.",
          "$ref": "#/$defs/url"
        },
        "path": {
          "description": "The local directory to download into.",
          "$ref": "#/$defs/dir"
        },
        "action": {
          "description": "What to do with the downloaded content (treated as another dependency).",
          "$ref": "#/$defs/dependency"
        }
      },
      "required": ["url", "path", "action"],
      "additionalProperties": false
    },

    "dependencyInstalled": {
      "description": "An installed (system-level) dependency, identified by name.",
      "type": "object",
      "properties": {
        "name": {
          "description": "The canonical name of the installed package.",
          "$ref": "#/$defs/name"
        },
        "alias": {
          "description": "The toplevel namespace under which this package is imported in the project. Defaults to the package name if omitted.",
          "$ref": "#/$defs/name"
        }
      },
      "required": ["name"],
      "additionalProperties": false
    },

    "dependencyLocal": {
      "description": "A local dependency defined in a *.toml file on disk.",
      "type": "object",
      "properties": {
        "path": {
          "description": "Path to the dependency's .toml file. Defaults to the current file.",
          "$ref": "#/$defs/file"
        },
        "name": {
          "description": "The name of the group within that file to depend on.",
          "type": "string"
        },
        "alias": {
          "description": "The toplevel namespace under which this dependency is imported. Defaults to the group name if omitted.",
          "type": "string"
        }
      },
      "required": ["name"],
      "additionalProperties": false
    },

    "dependencyShort": {
      "description": "A shorthand local dependency: just a name, equivalent to a dependencyLocal with only the name field set (path defaults to the current file).",
      "$ref": "#/$defs/name"
    },

    "dependency": {
      "description": "A dependency is any one of the four forms: external, installed, local, or shorthand.",
      "anyOf": [
        { "$ref": "#/$defs/dependencyExternal" },
        { "$ref": "#/$defs/dependencyInstalled" },
        { "$ref": "#/$defs/dependencyLocal" },
        { "$ref": "#/$defs/dependencyShort" }
      ]
    },

    "group": {
      "description": "A group (also called a theory) is the unit of modularity in STELF. Each group has a name, a root file, source directories, and dependencies.",
      "type": "object",
      "properties": {
        "name": {
          "description": "The name of this group, used to refer to it as a dependency.",
          "$ref": "#/$defs/name"
        },
        "main": {
          "description": "The entry-point file loaded when this group is imported. It is responsible for opening (re-exporting) other files in the group.",
          "$ref": "#/$defs/file"
        },
        "src": {
          "description": "Source directories that form the base search paths for this group's files. Omission is equivalent to a list containing only \".\".",
          "type": "array",
          "items": { "$ref": "#/$defs/dir" }
        },
        "dependencies": {
          "description": "The list of other groups this group depends on. Omission is equivalent to an empty list.",
          "type": "array",
          "items": { "$ref": "#/$defs/dependency" }
        },
        "local": {
          "description": "If true, this group cannot be used as a dependency by other groups; it can only be loaded directly at the REPL or CLI. Defaults to false.",
          "type": "boolean"
        }
      },
      "required": ["name", "main"],
      "additionalProperties": false
    }
  }
}|json}

let stelf_toml_prefix =
  {toml|#:schema ./stelf.schema.json

[[group]]
name = "|toml}

let stelf_toml_suffix =
  {toml|"
main = "src/main.lf"
src = ["src"]
dependencies = []
|toml}

let setup ?dir name : (unit, [ `Msg of string ]) result =
  let* () = validate_name name in
  let* dir = match dir with Some d -> Ok d | None -> Bos.OS.Dir.current () in
  let target = Fpath.(dir / name) in
  let* created = Bos.OS.Dir.create target in
  if not created then
    Error (`Msg (Fmt.str "directory %a already exists" Fpath.pp target))
  else
    let* (_ : bool) = Bos.OS.Dir.create Fpath.(target / "src") in
    let* () = Bos.OS.File.write Fpath.(target / "run.t") run_t in
    let* () = Bos.OS.File.write Fpath.(target / "dune") dune_file in
    let* () =
      Bos.OS.File.write Fpath.(target / "stelf.schema.json") schema_json
    in
    let* () = Bos.OS.File.write Fpath.(target / "src" / "main.lf") main_lf in
    let* () =
      Bos.OS.File.write
        Fpath.(target / "stelf.toml")
        (stelf_toml_prefix ^ name ^ stelf_toml_suffix)
    in
    Ok ()
