(* Core -- infrastructure shared by every refactoring pass.

   Passes operate on the Parsetree (no type information) and rewrite by splicing
   byte ranges into the original source text, so comments and layout survive and
   paren-matching edge cases that defeat a regex rewriter cannot arise. Every
   rewrite a pass declines is backstopped by the type checker, so conservatism is
   always safe.

   See docs/curry-reconciliation.md for the safety-argument template each pass
   follows. *)

open Parsetree
open Asttypes

let scan_roots = [ "src"; "test"; "bin" ]
let excluded_dirs = [ "_build"; ".git"; "basis"; "twelf"; "tools"; "examples"; "exercises" ]

(* ------------------------------------------------------------------ *)
(* File helpers                                                        *)
(* ------------------------------------------------------------------ *)

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let write_file path s =
  let oc = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () -> output_string oc s)

let rec walk acc dir =
  match Sys.readdir dir with
  | exception Sys_error _ -> acc
  | entries ->
      Array.fold_left
        (fun acc e ->
          let p = Filename.concat dir e in
          if Sys.is_directory p then
            if List.mem e excluded_dirs then acc else walk acc p
          else if Filename.check_suffix p ".ml" || Filename.check_suffix p ".mli" then p :: acc
          else acc)
        acc entries

let all_files roots = List.concat_map (fun r -> walk [] r) roots |> List.sort compare

type parsed = Impl of structure | Intf of signature

let parse_string path src =
  let lb = Lexing.from_string src in
  Location.init lb path;
  if Filename.check_suffix path ".mli" then Intf (Parse.interface lb)
  else Impl (Parse.implementation lb)

let parse_file path =
  let src = read_file path in
  (src, parse_string path src)
(* ------------------------------------------------------------------ *)
(* Source-text utilities                                               *)
(* ------------------------------------------------------------------ *)

let sub src (l : Location.t) = String.sub src l.loc_start.pos_cnum (l.loc_end.pos_cnum - l.loc_start.pos_cnum)
let is_ws c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

let rec skip_ws_back src i = if i >= 0 && is_ws src.[i] then skip_ws_back src (i - 1) else i
let rec skip_ws_fwd src i = if i < String.length src && is_ws src.[i] then skip_ws_fwd src (i + 1) else i

(* Index of the ')' matching the '(' at [i], or None. Naive w.r.t. comments and
   strings, which is safe here: it is only ever called on a range the parser
   already told us is a single expression. *)
let match_paren src i =
  let n = String.length src in
  let rec go i d =
    if i >= n then None
    else
      match src.[i] with
      | '(' -> go (i + 1) (d + 1)
      | ')' -> if d = 1 then Some i else go (i + 1) (d - 1)
      | _ -> go (i + 1) d
  in
  if i < n && src.[i] = '(' then go i 0 else None

(* If [s,e) is wrapped in a redundant matched paren pair, widen to include it.
   Handles the case where a node's location excludes its own parentheses. *)
let expand_parens src s e =
  let b = skip_ws_back src (s - 1) in
  if b >= 0 && src.[b] = '(' then
    match match_paren src b with
    | Some close when skip_ws_fwd src e = close -> (b, close + 1)
    | _ -> (s, e)
  else (s, e)

(* Does the text stand alone as a function argument without added parens? *)
let is_atom t =
  let t = String.trim t in
  let n = String.length t in
  if n = 0 then false
  else
    let ident =
      (t.[0] = '_' || (t.[0] >= 'a' && t.[0] <= 'z') || (t.[0] >= 'A' && t.[0] <= 'Z'))
      && String.for_all
           (fun c ->
             (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
             || c = '_' || c = '\'' || c = '.')
           t
    in
    if ident then true
    else if String.for_all (fun c -> c >= '0' && c <= '9') t then true
    else if t.[0] = '(' then match_paren t 0 = Some (n - 1)
    else if t.[0] = '[' then t.[n - 1] = ']'
    else false

let wrap t = if is_atom t then String.trim t else "(" ^ t ^ ")"
(* ------------------------------------------------------------------ *)
(* Edits                                                               *)
(* ------------------------------------------------------------------ *)

type edit = {
  file : string;
  s : int;
  e : int;
  repl : string;
  kind : string;  (* SIG | DEF | DEFFUN | CALL | ESCALATE *)
  line : int;
  note : string;
}

let edits : edit list ref = ref []
let add ed = edits := ed :: !edits

(* Reconciliation counters: every application of a target name that the tool
   declines is tallied by reason, so the delta against the independent scan can
   be explained category by category rather than by a percentage. *)
let diag : (string, int) Hashtbl.t = Hashtbl.create 16
let bump k = Hashtbl.replace diag k (1 + try Hashtbl.find diag k with Not_found -> 0)

(* Identifiers already present in a file -- used to pick non-shadowing parameter
   names when rewriting a `function`-bodied definition.

   Whole-file scope is what makes this sound, including against names a file
   inherits from an `open`. To be broken by shadowing, a case body would have to
   *reference* the shadowed name, which means writing it -- so it would appear as
   a token here and the candidate would be rejected. Shadowing a binding that the
   body never mentions is inert. *)
let file_words src =
  let tbl = Hashtbl.create 1024 in
  let n = String.length src in
  let buf = Buffer.create 32 in
  let flush () =
    if Buffer.length buf > 0 then (Hashtbl.replace tbl (Buffer.contents buf) (); Buffer.clear buf)
  in
  for i = 0 to n - 1 do
    let c = src.[i] in
    if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_' || c = '\''
    then Buffer.add_char buf c
    else flush ()
  done;
  flush ();
  tbl

let fresh_names words arity =
  let base = [| "a"; "b"; "c"; "d" |] in
  let rec try_suffix k =
    let cand = List.init arity (fun i -> base.(i) ^ if k = 0 then "" else string_of_int k) in
    if List.exists (fun c -> Hashtbl.mem words c) cand then try_suffix (k + 1) else cand
  in
  try_suffix 0
(* ------------------------------------------------------------------ *)
(* Driver                                                              *)
(* ------------------------------------------------------------------ *)

let escape s =
  String.concat "\\n" (String.split_on_char '\n' s) |> fun s ->
  if String.length s > 90 then String.sub s 0 90 ^ "..." else s

(* Nested call sites produce overlapping ranges (`f (g (a,b), c)`). Keep the
   outer edit and drop the inner one.

   Return the dropped *edits*, not a count. A fresh `curry patch` invocation does
   NOT pick them up: `collect_targets` reads the tree as it finds it, so once run
   1 has rewritten `val g : a * b -> c` to `val g : a -> b -> c`, `g` is no
   longer a target and the deferred inner `g (a, b)` is never looked at again --
   it survives as a type error with no row in curry-sites.txt pointing at it.
   `patch` therefore loops in-process (see patch_rounds), where `targets` stays
   populated across rounds. *)
let non_overlapping eds =
  (* Group by file first -- offsets from different files are incomparable. *)
  let sorted =
    List.sort
      (fun a b ->
        match compare a.file b.file with
        | 0 -> ( match compare a.s b.s with 0 -> compare b.e a.e | c -> c)
        | c -> c)
      eds
  in
  let kept, dropped, _, _ =
    List.fold_left
      (fun (kept, dropped, cur_file, last_end) ed ->
        if ed.file <> cur_file then (ed :: kept, dropped, ed.file, ed.e)
        else if ed.s >= last_end then (ed :: kept, dropped, cur_file, ed.e)
        else (kept, ed :: dropped, cur_file, last_end))
      ([], [], "", min_int) sorted
  in
  (List.rev kept, List.rev dropped)

(* ------------------------------------------------------------------ *)
(* Splicing and AST verification                                       *)
(* ------------------------------------------------------------------ *)

(* Descending by offset so earlier ranges stay valid. *)
let splice src eds =
  List.fold_left
    (fun acc e -> String.sub acc 0 e.s ^ e.repl ^ String.sub acc e.e (String.length acc - e.e))
    src
    (List.sort (fun a b -> compare b.s a.s) eds)

(* The type checker catches shape errors; it does not catch reassociation.
   Rewriting `let _ = e in body` to `ignore e; body` under `if c then ...` gives
   `(if c then ignore e); body`, which still typechecks whenever the `if` has no
   `else` -- and then runs `body` unconditionally. And a `begin`/`end` strip has
   no AST footprint at all, because `begin e end` and `(e)` parse identically:
   there is no node to match on, so nothing but a reparse can check it.

   A pass therefore declares the transformation it *intends* as a mapper over the
   original tree. Core reparses the patched text and requires the two to agree
   once locations are erased. `Ast_mapper.default_mapper` as the intent means
   "this rewrite must not change the tree at all".

   Note what this does NOT cover: renaming. Capture is a scoping property, not a
   shape one -- `g_` -> `g` yields the intended AST whether or not it captures a
   binding. Passes that rebind names need their own scope argument. *)

let loc_eraser = { Ast_mapper.default_mapper with location = (fun _ _ -> Location.none) }
let erase = function
  | Impl st -> Impl (loc_eraser.structure loc_eraser st)
  | Intf sg -> Intf (loc_eraser.signature loc_eraser sg)

let map_parsed (m : Ast_mapper.mapper) = function
  | Impl st -> Impl (m.structure m st)
  | Intf sg -> Intf (m.signature m sg)

(* None on success, Some reason on failure. *)
let verify ~path ~src ~original ~intent eds =
  match parse_string path (splice src eds) with
  | exception e -> Some ("patched text does not parse: " ^ Printexc.to_string e)
  | got -> if erase got = erase (map_parsed intent original) then None else Some "AST differs from intent"

(* Apply a round's edits. Bottom-up within each file so earlier ranges stay
   valid. Returns (edits applied, files written). *)
let apply kept =
  let by_file = Hashtbl.create 64 in
  List.iter
    (fun e ->
      let cur = try Hashtbl.find by_file e.file with Not_found -> [] in
      Hashtbl.replace by_file e.file (e :: cur))
    kept;
  let nf = ref 0 and ne = ref 0 in
  Hashtbl.iter
    (fun f eds ->
      let src = read_file f in
      ne := !ne + List.length eds;
      let out = splice src eds in
      if out <> src then (write_file f out; incr nf))
    by_file;
  (!ne, !nf)
