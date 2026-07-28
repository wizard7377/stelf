(** Ghost-position detection for parse trees.

    A parse tree is only useful for error messages (and, later, editor
    integration) if every node can be pointed back at a span of the input. This
    module recursively walks a parsed tree and reports every node whose source
    location is the {e ghost} location.

    {2 What "ghost" means here}

    [Cst.loc] is [{ start_pos : int; end_pos : int }] -- a pair of byte offsets
    into the input string. There is no file field and no line/column, so the
    ghost location is simply [{0; 0}] and not, as one might expect, a position
    in some [<INTERACTIVE>] pseudo-file.

    [Cst.View.Loc.view] never actually returns [Ghost]; it unconditionally
    returns [Loc (None, start_pos, end_pos)]. So the check is on the value
    [(0, 0)], with the [Ghost] branch kept only so this keeps working if the
    view is ever made faithful. The accepted false positive: a genuine
    zero-width span at offset 0 is indistinguishable from a ghost through the
    public API.

    We only ever check that a position is {e not} ghost, never that it is
    correct -- a location of [(1000, 1)] on a four-line input passes.

    {2 How this check could come to under-report}

    [Modern.loc_union] has [Ghost] branches that are dead for the reason above,
    so combining a ghost with a real location yields
    [mk_loc (min 0 s) (max 0 e)] = [(0, e)] rather than propagating the ghost.
    That is not [(0, 0)], so a laundered position would pass this check wearing
    a plausible-looking span anchored at offset 0.

    No parser path reaches that today: the only remaining source of a ghost term
    location is [Modern.term_loc]'s [Internal] branch, and [Internal] is a de
    Bruijn reference the parser never builds. But anything that reintroduces a
    ghost term location upstream of a [loc_union] will be silently absorbed
    rather than caught here, and a [(0, e)] span covering input the node does
    not span is the tell. *)

module Cst = Modern.Modern.Cst
module V = Cst.View

type path = string list
(** A breadcrumb trail from the root down to a node, innermost segment first.
    Findings are reported with the full trail so that a red test names the node
    that is missing a position rather than merely asserting one exists. *)

let render (path : path) : string = String.concat " -> " (List.rev path)
let down (path : path) (label : string) : path = label :: path
let idx (path : path) (i : int) : path = Printf.sprintf "[%d]" i :: path

let is_ghost (l : V.Loc.t) : bool =
  match V.Loc.view l with
  | V.Loc.Ghost -> true
  | V.Loc.Loc (_, 0, 0) -> true
  | V.Loc.Loc _ -> false

(** [check path label l] reports a finding if [l] is the ghost location. *)
let check (path : path) (label : string) (l : V.Loc.t) : string list =
  if is_ghost l then [ render (down path label) ] else []

(** Walk each element of a list, tagging children with their index. *)
let each (f : path -> 'a -> string list) (path : path) (xs : 'a list) :
    string list =
  List.concat (List.mapi (fun i x -> f (idx path i) x) xs)

let names_label (kind : string) (names : string option list) : string =
  let shown =
    List.map (function Some n -> n | None -> "_") names |> String.concat " "
  in
  if shown = "" then kind else kind ^ " " ^ shown

(* {2 Terms and declarations} *)

let rec walk_term (path : path) (t : V.Term.t) : string list =
  let u = V.Term.view t in
  let open V.Term in
  match u with
  | Lowercase (l, (_, n)) -> check path ("Term.Lowercase " ^ n) l
  | Uppercase (l, (_, n)) -> check path ("Term.Uppercase " ^ n) l
  | Qualified (l, (_, n), _) -> check path ("Term.Qualified " ^ n) l
  | Text (l, _) -> check path "Term.Text" l
  | ExistVar (l, n) -> check path ("Term.ExistVar " ^ n) l
  | FreeVar (l, n) -> check path ("Term.FreeVar " ^ n) l
  | Omitted l -> check path "Term.Omitted" l
  | Typ l -> check path "Term.Typ" l
  | MacroParam (l, _, _) -> check path "Term.MacroParam" l
  (* [Term.view] flattens nested [Pi_]/[Lam_]/[App_] into n-ary form and keeps
     only the outermost location, so the inner spine locations are neither
     checked nor checkable through the view. *)
  | Pi (l, ds, body) ->
      let p = down path "Term.Pi" in
      check path "Term.Pi" l @ each walk_decl p ds @ walk_term p body
  | Lam (l, ds, body) ->
      let p = down path "Term.Lam" in
      check path "Term.Lam" l @ each walk_decl p ds @ walk_term p body
  | App (l, head, args) ->
      let p = down path "Term.App" in
      check path "Term.App" l @ walk_term p head @ each walk_term p args
  | HasType (l, tm, ty) ->
      let p = down path "Term.HasType" in
      check path "Term.HasType" l @ walk_term p tm @ walk_term p ty
  | Arrow (l, a, b) ->
      let p = down path "Term.Arrow" in
      check path "Term.Arrow" l @ walk_term p a @ walk_term p b
  | BackArrow (l, a, b) ->
      let p = down path "Term.BackArrow" in
      check path "Term.BackArrow" l @ walk_term p a @ walk_term p b
  | Foreign (l, tm) ->
      let p = down path "Term.Foreign" in
      check path "Term.Foreign" l @ walk_term p tm
  | Local (l, _, tm) ->
      let p = down path "Term.Local" in
      check path "Term.Local" l @ walk_term p tm
  (* [Internal] is a printer-internal node with no surface syntax, so it is
     never produced by the parser. Its location is whatever the resugarer put
     there (normally [ghost]); walking it would flag that as a defect. *)
  | Internal _ -> []

and walk_decl (path : path) (d : V.Decl.t) : string list =
  match V.Decl.view d with
  | V.Decl.Decl1 (l, names, typ, _body) ->
      (* The fourth field is always a fabricated [Omitted_ ghost] synthesised by
         [Decl.view] and discarded again by [Decl.review]; descending into it
         would flag every binder in the corpus on a view artifact rather than on
         a genuinely missing position. *)
      let label = names_label "Decl1" names in
      let p = down path label in
      check path label l @ walk_term p typ
  | V.Decl.Decl0 (l, names, typ) ->
      let label = names_label "Decl0" names in
      let p = down path label in
      check path label l @ walk_term p typ

(* {2 Commands}

   Note that [cmd], [mode], [fixity], [block_item], [query], [define] and
   [solve] carry no location field in the concrete CST at all: [Cmd.view] and
   friends synthesise [ghost] unconditionally and [review] drops any location
   handed to them. Findings on these nodes are therefore structural -- the
   parser does compute a real location for most of them, but the CST has
   nowhere to put it. *)

let walk_mode (path : path) (m : V.Mode.t) : string list =
  match V.Mode.view m with
  | V.Mode.Plus l -> check path "Mode.Plus" l
  | V.Mode.Star l -> check path "Mode.Star" l
  | V.Mode.Minus l -> check path "Mode.Minus" l
  | V.Mode.Minus1 l -> check path "Mode.Minus1" l

let rec walk_mode_spine (path : path) (s : V.Mode.Spine.t) : string list =
  match V.Mode.Spine.view s with
  | V.Mode.Spine.ModeNil l -> check path "Mode.Spine.ModeNil" l
  | V.Mode.Spine.ModeApp (l, (m, _), rest) ->
      let p = down path "Mode.Spine.ModeApp" in
      check path "Mode.Spine.ModeApp" l @ walk_mode p m @ walk_mode_spine p rest

let rec walk_mode_term (path : path) (t : V.Mode.Term.t) : string list =
  match V.Mode.Term.view t with
  | V.Mode.Term.ModeTerm (l, (_, n), spine) ->
      let label = "Mode.Term.ModeTerm " ^ n in
      let p = down path label in
      check path label l @ walk_mode_spine p spine
  | V.Mode.Term.ModePi (l, d, a, b) ->
      let p = down path "Mode.Term.ModePi" in
      check path "Mode.Term.ModePi" l
      @ walk_decl p d @ walk_mode_term p a @ walk_mode_term p b

let walk_mode_dec (path : path) (d : V.Mode.Dec.t) : string list =
  match V.Mode.Dec.view d with
  | V.Mode.Dec.ModeDec (l, modes, term) ->
      let p = down path "Mode.Dec.ModeDec" in
      check path "Mode.Dec.ModeDec" l
      @ each (fun p (m, _) -> walk_mode p m) p modes
      @ walk_mode_term p term

let walk_query (path : path) (q : V.Query.t) : string list =
  match V.Query.view q with
  | V.Query.Query (l, _, tm) ->
      let p = down path "Query" in
      check path "Query" l @ walk_term p tm

let walk_define (path : path) (d : V.Define.t) : string list =
  match V.Define.view d with
  | V.Define.Define (l, _, tm, ty) -> (
      let p = down path "Define" in
      check path "Define" l @ walk_term p tm
      @ match ty with Some ty -> walk_term p ty | None -> [])

let walk_solve (path : path) (s : V.Solve.t) : string list =
  match V.Solve.view s with
  | V.Solve.Solve (l, _, tm) ->
      let p = down path "Solve" in
      check path "Solve" l @ walk_term p tm

let walk_block_item (path : path) (b : V.BlockItem.t) : string list =
  match V.BlockItem.view b with
  | V.BlockItem.Any (l, d) ->
      let p = down path "BlockItem.Any" in
      check path "BlockItem.Any" l @ walk_decl p d
  | V.BlockItem.All (l, d) ->
      let p = down path "BlockItem.All" in
      check path "BlockItem.All" l @ walk_decl p d

let walk_fixity (path : path) (f : V.Fixity.t) : string list =
  match V.Fixity.view f with
  | V.Fixity.Left l -> check path "Fixity.Left" l
  | V.Fixity.Right l -> check path "Fixity.Right" l
  | V.Fixity.Prefix l -> check path "Fixity.Prefix" l
  | V.Fixity.Postfix l -> check path "Fixity.Postfix" l
  | V.Fixity.Middle l -> check path "Fixity.Middle" l
  | V.Fixity.None l -> check path "Fixity.None" l

let rec walk_order (path : path) (o : V.Thm.Order.t) : string list =
  match V.Thm.Order.view o with
  | V.Thm.Order.Varg (l, _) -> check path "Order.Varg" l
  | V.Thm.Order.Lex (l, os) ->
      let p = down path "Order.Lex" in
      check path "Order.Lex" l @ each walk_order p os
  | V.Thm.Order.Simul (l, os) ->
      let p = down path "Order.Simul" in
      check path "Order.Simul" l @ each walk_order p os

let rec walk_cmd (path : path) (c : V.Cmd.t) : string list =
  let u = V.Cmd.view c in
  let open V.Cmd in
  (* [here label l children] checks this node then descends. *)
  let here label l children = check path label l @ children (down path label) in
  let none _ = [] in
  match u with
  | Query (l, _, _, _, q) -> here "Cmd.Query" l (fun p -> walk_query p q)
  | QueryTabled (l, _, _, _, q) ->
      here "Cmd.QueryTabled" l (fun p -> walk_query p q)
  | AdhocQuery (l, q) -> here "Cmd.AdhocQuery" l (fun p -> walk_query p q)
  | Unique (l, tm) -> here "Cmd.Unique" l (fun p -> walk_term p tm)
  | Mode (l, md) -> here "Cmd.Mode" l (fun p -> walk_mode_dec p md)
  | Define (l, d) -> here "Cmd.Define" l (fun p -> walk_define p d)
  | DeclCmd (l, tm) -> here "Cmd.DeclCmd" l (fun p -> walk_term p tm)
  | Inline (l, n, tm) -> here ("Cmd.Inline " ^ n) l (fun p -> walk_term p tm)
  | Symbol (l, n, _) -> here ("Cmd.Symbol " ^ n) l none
  | Freeze (l, _) -> here "Cmd.Freeze" l none
  | Thaw (l, _) -> here "Cmd.Thaw" l none
  | Sort (l, _, ds) -> here "Cmd.Sort" l (fun p -> each walk_decl p ds)
  | Term (l, d) -> here "Cmd.Term" l (fun p -> walk_decl p d)
  | Block (l, n, items) ->
      here ("Cmd.Block " ^ n) l (fun p -> each walk_block_item p items)
  | Union (l, n, _) -> here ("Cmd.Union " ^ n) l none
  | Worlds (l, _, tms) -> here "Cmd.Worlds" l (fun p -> each walk_term p tms)
  | Deterministic (l, _) -> here "Cmd.Deterministic" l none
  | Eval (l, cs) -> here "Cmd.Eval" l (fun p -> each walk_cmd p cs)
  | Prec (l, fx, _, _) -> here "Cmd.Prec" l (fun p -> walk_fixity p fx)
  | Solve (l, s) -> here "Cmd.Solve" l (fun p -> walk_solve p s)
  | Stop (l, ()) -> here "Cmd.Stop" l none
  | ReplQuit (l, ()) -> here "Cmd.ReplQuit" l none
  | ReplHelp (l, _) -> here "Cmd.ReplHelp" l none
  | ReplGet (l, _) -> here "Cmd.ReplGet" l none
  | ReplSet (l, _, _) -> here "Cmd.ReplSet" l none
  | ReplVersion (l, ()) -> here "Cmd.ReplVersion" l none
  | Total (l, os, tms) ->
      here "Cmd.Total" l (fun p -> each walk_order p os @ each walk_term p tms)
  | Terminates (l, os, tms) ->
      here "Cmd.Terminates" l (fun p ->
          each walk_order p os @ each walk_term p tms)
  | Covers (l, md) -> here "Cmd.Covers" l (fun p -> walk_mode_dec p md)
  | Name (l, _) -> here "Cmd.Name" l none
  | Prose (l, _) -> here "Cmd.Prose" l none
  | Reduces (l, n, tms) ->
      here ("Cmd.Reduces " ^ n) l (fun p -> each walk_term p tms)
  | Macro (l, _, n, body) ->
      here ("Cmd.Macro " ^ n) l (fun p -> walk_cmd p body)
  | Seq (l, items) ->
      here "Cmd.Seq" l (fun p ->
          each
            (fun p item ->
              match item with Outer _ -> [] | Cmd c -> walk_cmd p c)
            p items)
  | Require (l, _) -> here "Cmd.Require" l none
  | Open (l, _) -> here "Cmd.Open" l none
  | Scope (l, n, body) -> here ("Cmd.Scope " ^ n) l (fun p -> walk_cmd p body)
  | Use (l, _, tms) -> here "Cmd.Use" l (fun p -> each walk_term p tms)
