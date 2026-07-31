type status = Works | Caveat of string | Stub of string

type entry = {
  name : string;
  aliases : string list;
  summary : string;
  status : status;
}

type category = { title : string; slug : string; entries : entry list }

let cat title slug entries = { title; slug; entries }

let e ?(status = Works) ?(aliases = []) name summary =
  { name; aliases; summary; status }

(* One entry per alternative in Cmd.ml's [choice], in the category order of
   hacking/grammar/stelf.md §6. *)
let categories =
  [
    (* §6.1 *)
    cat "Declaring constants" "constants"
      [
        e "sort" "declare a type family: %sort NAMES DECL*";
        e "term" "declare a term constant: %term DECL";
        e "def" "define a constant opaquely; also spelled %define"
          ~aliases:[ "define" ];
        e "inline" "define a constant transparently — always unfolded";
        e "block" "declare a context block: [x T] a some, {x T} a hypothesis";
        e "union" "declare a block as the union of others";
        e "symbol" "alias a name"
          ~status:(Caveat "names only — it cannot alias keywords");
        e "decl" "print a name's declaration";
      ];
    (* §6.2 — these expand entirely in the parser *)
    cat "Derived forms" "derived"
      [
        e "data" "%sort + %scope: a family and its constructors as one unit";
        e "prop" "%sort + %mode: a judgement's arguments written once";
        e "proof" "%sort + %scope + %mode + %worlds + %total";
      ];
    (* §6.3 *)
    cat "Modes, worlds and totality" "modes"
      [
        e "mode" "declare argument modes: %in %out %out1 %star";
        e "worlds" "declare which blocks a family lives in";
        e "total" "assert and check totality at a termination order";
        e "terminates" "assert termination at an order";
        e "covers" "check that a family's cases are exhaustive";
        e "reduces" "assert a relation (< <= > >= =) between arguments";
        e "freeze" "forbid further constructors for a family";
        (* Impl.ml gates %thaw on Global.unsafe, which in this frontend nothing
           writes -- the only assignment in the tree is the legacy server's
           `set unsafe' (Server_.ml:174). So it always fails here. *)
        e "thaw" "undo %freeze"
          ~status:(Stub "needs the unsafe flag; nothing sets it");
        e "deterministic" "mark a family as having at most one solution";
        e "unique" "check a family's uniqueness against its mode";
      ];
    (* §6.4 *)
    cat "Queries" "queries"
      [
        e "query" "search for solutions: three bounds, _ meaning unbounded";
        e "querytabled" "%query using the tabled solver";
        e "?" "unbounded query, meant for the REPL: %? EXPR";
        e "solve" "find one solution and install it as a constant";
      ];
    (* §6.5, detailed in §7 *)
    cat "Scopes, modules and files" "files"
      [
        e "scope" "group declarations under a name; reopens if it exists";
        e "open" "promote a scope's members to bare visibility";
        e "require" "load a file by path; idempotent, and cycles terminate";
        e "eval" "run a %{ ... %} block as a single unit";
        e "use" "instantiate a module"
          ~status:(Stub "not implemented in this frontend");
      ];
    (* §5.1 *)
    cat "Fixity" "fixity"
      [ e "prec" "declare fixity and precedence: %prec FIXITY LEVEL NAMES" ];
    (* §6.7 *)
    cat "Annotations" "annotations"
      [
        e "name" "suggest variable names" ~status:(Stub "accepted, ignored");
        e "prose" "mark a name as prose" ~status:(Stub "accepted, ignored");
      ];
    (* §6.6 *)
    cat "REPL and meta" "meta"
      [
        e "help" "this list; %help NAME or %help CATEGORY for one part of it";
        e "version" "print the version";
        (* Impl.Options is a bare hashtable that nothing outside %get reads, so
           these two are a scratchpad rather than a settings interface. *)
        e "get" "read back a key set by %set"
          ~status:(Caveat "affects nothing yet");
        e "set" "store a key: %set KEY VALUE"
          ~status:(Caveat "readable by %get only");
        e "quit" "leave the REPL — Ctrl-D also works";
      ];
    cat "Separator" "separator"
      [ e "." "end the current command; every command ends with %." ];
  ]

let entries = List.concat_map (fun c -> c.entries) categories

(* Aliases are looked up too, so a spelling the summary itself advertises —
   %help define, for %def — does not fall through to "no such command". *)
let find n =
  List.find_opt
    (fun x -> String.equal x.name n || List.exists (String.equal n) x.aliases)
    entries

(* The overview is ONE Reply.Response carrying one multi-line string. Both
   renderers prefix a Response with the literal 3 characters "=> " — and only on
   its first line — so every later line is indented by [cont] to align under it.
   Emitting one Response per line instead would stamp "=> " on all fifty. *)
let cont = "   "

let pad (w : int) (s : string) : string =
  s ^ String.make (Stdlib.max 0 (w - String.length s)) ' '

let name_width =
  List.fold_left (fun acc x -> Stdlib.max acc (String.length x.name)) 0 entries
  + 1 (* the % *) + 2 (* gutter *)

let status_note = function
  | Works -> ""
  | Caveat s -> "  (" ^ s ^ ")"
  | Stub s -> "  [" ^ s ^ "]"

(* A blank separator gets no indent: [cont] exists to align text under the "=> "
   prefix, and padding an empty line only leaves trailing whitespace. *)
let buf_line b s =
  if not (String.equal s "") then begin
    Buffer.add_string b cont;
    Buffer.add_string b s
  end;
  Buffer.add_char b '\n'

let buf_entry b x =
  buf_line b
    ("  " ^ pad name_width ("%" ^ x.name) ^ x.summary ^ status_note x.status)

let buf_category b c =
  buf_line b "";
  buf_line b c.title;
  List.iter (buf_entry b) c.entries

let overview =
  let b = Buffer.create 4096 in
  (* First line only: this is what the "=> " prefix lands on. *)
  Buffer.add_string b
    "STELF commands. Every command begins with % and is submitted by %.\n";
  buf_line b "e.g.  %sort nat %.        %term zero nat %.";
  buf_line b
    "%help NAME %. describes one command — write the name bare, as %help sort";
  List.iter (buf_category b) categories;
  buf_line b "";
  buf_line b "Full reference: hacking/grammar/stelf.md \xc2\xa76";
  Buffer.contents b

(* Wrap a comma-separated list into lines of at most [width] characters, so that
   adding a category later cannot silently push the line past a terminal's
   80 columns -- where the overflow would land at column 0 and break the
   alignment the whole layout is built on. *)
let wrap_items ~(width : int) (items : string list) : string list =
  let rec go acc cur = function
    | [] -> List.rev (if String.equal cur "" then acc else cur :: acc)
    | it :: rest ->
        let cand = if String.equal cur "" then it else cur ^ ", " ^ it in
        if String.length cand <= width then go acc cand rest
        else go (cur :: acc) it rest
  in
  go [] "" items

(* The wrap breaks between items, so the separating comma has to be re-added at
   the seam; the final line gets the full stop instead. *)
let category_lines =
  match
    List.rev (wrap_items ~width:66 (List.map (fun c -> c.slug) categories))
  with
  | [] -> []
  | last :: rest -> List.rev ((last ^ ".") :: List.map (fun l -> l ^ ",") rest)

let topic (t : string) : string =
  (* A leading % is what a user will type despite the help text saying otherwise.
     The parser cannot actually deliver one here (parse_var rejects it), but strip
     it anyway so this function is correct on its own terms. *)
  let t =
    if String.length t > 0 && Char.equal t.[0] '%' then
      String.sub t 1 (String.length t - 1)
    else t
  in
  match find t with
  | Some x ->
      let b = Buffer.create 256 in
      Buffer.add_string b
        ("%" ^ x.name ^ " — " ^ x.summary ^ status_note x.status ^ "\n");
      buf_line b
        "There is no per-command manual; see hacking/grammar/stelf.md \
         \xc2\xa76.";
      buf_line b "%help %. lists every command.";
      Buffer.contents b
  | None -> (
      match List.find_opt (fun c -> String.equal c.slug t) categories with
      | Some c ->
          let b = Buffer.create 512 in
          Buffer.add_string b (c.title ^ "\n");
          List.iter (buf_entry b) c.entries;
          Buffer.contents b
      | None ->
          let b = Buffer.create 256 in
          Buffer.add_string b ("No command or category named '" ^ t ^ "'.\n");
          buf_line b "%help %. lists every command. Categories:";
          List.iter (fun l -> buf_line b ("  " ^ l)) category_lines;
          Buffer.contents b)
