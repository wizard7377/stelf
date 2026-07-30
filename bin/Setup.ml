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

(* The one thing a template cannot know is what the project is called, so it
   asks: every occurrence of [{{name}}] is replaced. Nothing else is
   interpreted -- a template is copied out byte for byte otherwise, which is
   what lets [stelf.schema.json] stay valid JSON and [dune] stay a dune file
   while sitting in the source tree. *)
let placeholder = "{{name}}"

let expand ~name template =
  let buf = Buffer.create (String.length template) in
  let n = String.length template and k = String.length placeholder in
  let rec go i =
    if i >= n then Buffer.contents buf
    else if i + k <= n && String.sub template i k = placeholder then (
      Buffer.add_string buf name;
      go (i + k))
    else (
      Buffer.add_char buf template.[i];
      go (i + 1))
  in
  go 0

(* [Templates.files] is generated from [bin/templates/] by [Embed.ml]; adding a
   file there is all it takes to have [setup] write it. Directories come along
   with the files inside them, so an empty one cannot be expressed -- put a
   placeholder file in it if that is ever wanted. *)
let write_template ~name ~target (path, contents) =
  let dest = Fpath.(target // v path) in
  let* (_ : bool) = Bos.OS.Dir.create (Fpath.parent dest) in
  Bos.OS.File.write dest (expand ~name contents)

let setup ?dir name : (unit, [ `Msg of string ]) result =
  let* () = validate_name name in
  let* dir = match dir with Some d -> Ok d | None -> Bos.OS.Dir.current () in
  let target = Fpath.(dir / name) in
  let* created = Bos.OS.Dir.create target in
  if not created then
    Error (`Msg (Fmt.str "directory %a already exists" Fpath.pp target))
  else
    List.fold_left
      (fun acc file ->
        let* () = acc in
        write_template ~name ~target file)
      (Ok ()) Templates.files
