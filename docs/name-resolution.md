# How STELF name resolution works (`%scope`, `%open`, `%abs`, `%val`, `%( … )`)

A reference to the actual OCaml functions involved, traced through the four layers.
Files: `src/Fronts/Modern/` (parse), `src/Common/Cst/Cst.ml` (data), `src/Fronts/Pal/Impl.ml`
(install-time state), `src/Recon/ReconTerm.ml` (use-site resolution), `src/Names/Names_.ml`
(the lookup engine).

---

## 0. The two kinds of "visibility"

Everything below hinges on a distinction between two tables a name can live in:

- **Bare / global visibility** — the process-wide `topNamespace` (constants) and
  `topStructNamespace` (structures) hash tables in `Names_.ml`. A name here is reachable
  *unqualified*. Shadow-aware: installing a colliding name hides the old one and records the
  hidden cid so it can be restored on uninstall.
- **Qualified / namespace-local visibility** — a `namespace` value, which is a pair
  `(mid StringTree.table * cid StringTree.table)` (`Names_.ml:220`). Every module/structure
  owns one (its "components"), and the currently-loading `%require` group owns one
  (`currentGroupNamespace`). A name here is reachable only via its path (`Foo.bar`).

`%scope`, `%open`, `%abs`, `%val` are all about *which table a lookup consults and in what
order*.

---

## 1. Parsing — `src/Fronts/Modern/`

The modern angstrom parser turns surface syntax into CST nodes (the legacy `src/Frontend/`
parser does **not** know these directives):

| Surface | Parser location | Produces |
|---|---|---|
| `%scope NAME { … }` | `Cmd.ml:127-138` | `Cst.View.Cmd.review @@ Scope (loc, id, Eval body)` |
| `%open PATH…` | `Cmd.ml:275-278` | `Cst.View.Cmd.review @@ Open (loc, ids)` |
| `%val NAME` | `Modern.ml:297` | `Qualified (loc, qid, Cst.Val)` term |
| `%abs NAME` | `Modern.ml:298` | `Qualified (loc, qid, Cst.Abs)` term |
| `%( NAME S )` | `Modern.ml:299-302` | `Qualified (loc, qid, Cst.Val)` term |

## 2. CST representation — `src/Common/Cst/Cst.ml`

Pure data, no behavior:

- `type qid_form = Val | Abs` (`Cst.ml:24`) — carries the %val vs %abs choice on a
  `Quid_` / `Qualified` term. Its doc comment (`Cst.ml:17-23`) is the canonical spec and points
  at `Names.resolveQid`.
- `Open_ of string list` and `Scope_ of string * cmd` (`Cst.ml:206-207`) — the command
  constructors (View-wrapped as `Open` / `Scope`).

## 3. The lookup engine — `src/Names/Names_.ml`

### Types & tables
- `type qid = Qid of string list * string` (`:202`) — path + name. Helpers: `qidToString`,
  `stringToQid`, `validateQualName`, `unqualified`.
- `type namespace = mid StringTree.table * cid StringTree.table` (`:220`);
  `newNamespace ()` (`:223`) makes a fresh pair.
- Global bare tables (in the `open! struct … end` block, `:257-308`):
  `topNamespace` + `topInsert`/`topLookup`/`topDelete`/`topClear`;
  `topStructNamespace` + `topStructInsert`/…; the shadow bookkeeping arrays
  `shadowArray` / `structShadowArray`; per-cid `componentsArray` (a mid's `namespace`).

### Installation (writing names in)
- **Bare, shadow-aware:** `installConstName cid` (`:314`) — `topInsert`, and if it hid a prior
  cid, stash it in `shadowArray`. `installStructName mid` (`:346`) is the struct analogue.
- **Undo:** `uninstallConst cid` (`:327`) / `uninstallStruct mid` (`:354`) — delete, then
  restore whatever was in `shadowArray`/`structShadowArray`. This is what lets a `%scope`
  session be retracted cleanly.
- **Into a specific namespace (qualified):** `insertConst (ns, cid)` (`:225`, *fatal* on
  collision), `insertConstShadow (ns, cid)` (`:237`, *tolerant* — used inside `%scope`),
  `insertStruct (ns, mid)` (`:242`), plus `insertConstAlias` / `installAlias`.
- Iteration: `appConsts` / `appStructs` (`:254-255`) walk a namespace's tables.

### Lookup (reading names out)
- `constLookup qid` (`:512`) / `structLookup qid` (`:520`) — against the **global top** tables,
  drilling into structures along the path via `findTopStruct` (`:420`).
- `constLookupIn (ns, qid)` (`:452`) / `structLookupIn (ns, qid)` (`:460`) — against a
  **specific** namespace, drilling via `findStruct` (`:412`).
- Path helpers: `findStruct`, `findTopStruct`, `findUndefStruct`, `findTopUndefStruct`.
- Inverse ("is this name free?"): `constUndef` / `structUndef` / `constUndefIn` / `structUndefIn`.

### The dispatcher — `resolveQid` (`Names_.ml:553`)
```ocaml
let currentGroupNamespace : namespace ref = ref (newNamespace ())   (* :533 *)

let resolveQid ~shortest qid =
  match (shortest, qid) with
  | true, Qid ([], _) ->                        (* %abs NAME (unqualified) *)
      (match constLookupIn (!currentGroupNamespace, qid) with
       | Some _ as found -> found               (*  → group's own toplevel first *)
       | None -> constLookup qid)               (*  → else shadow-aware bare *)
  | _ -> constLookup qid                         (* %val / bare / %( ) / %abs(qualified) *)
```
- `shortest:false` (`%val`, bare name, `%( NAME )`) = plain `constLookup` — shadow-aware, so an
  open `%scope`'s binding wins ("longest match").
- `shortest:true` on a bare name (`%abs NAME`) = try `currentGroupNamespace` first (the genuine
  toplevel decl of the loading `%require` group, bypassing any live `%scope` shadow), fall back
  to `constLookup`.
- `shortest:true` on a qualified name = just `constLookup` (qualified lookup is shadow-immune).

## 4. Install-time state & directive execution — `src/Fronts/Pal/Impl.ml` (`module Install`)

This is the process-wide singleton (`Impl.Impl()`); its mutable state is the "current name
environment" while a signature loads.

### State
- `open_scope : (string * IntSyn.cid list ref) option ref` (`:220`) — the `%scope` session that
  is currently bare-visible: its name plus the cids installed under it (so they can be retracted).
- `current_group_ns` (`:90`) — **aliased** to `Names.currentGroupNamespace` (so `resolveQid`
  and this loop share one ref).

### The interpreter: `install1 ns cmd` (`:445`), with `install1_item`, `install`
- **Scope-boundary guard** (`:465-471`): before running any top-level command, if a session is
  open (`open_scope = Some …`) and the incoming command is *not* a same-name `%scope` reopen,
  retract it — `List.app Names.uninstallConst !cur_installs; open_scope := None`.
- `install_condec ?scope_installs ns cd` (`:160`): `IntSyn.sgnAdd` → `Names.installConstName`
  (bare) → then either `Names.insertConst (ns, cid)` (top level, fatal-on-collision) **or**, when
  inside a scope, `Names.insertConstShadow (ns, cid)` and push the cid onto `scope_installs`.

### `Cst.Open_ ids` (`:788-825`)
Resolve the module: `structLookupIn (ns,qid)` then fall back to `structLookup qid`; get its
members with `Names.getComponents mid`; then **promote to bare visibility** —
`Names.appConsts (fun (_,cid) -> Names.installConstName cid; …; Names.insertConst (ns,cid))` and
`Names.appStructs … Names.insertStruct`. If running inside a `%scope`, each promoted cid is also
pushed onto `scope_installs` so it retracts with the enclosing body.

### `Cst.Scope_ (name, body)` (`:826-871`)
1. Find-or-create the child structure: `Names.structLookupIn (ns, Qid([],name))` →
   `Names.getComponents`, or else `IntSyn.sgnStructAdd (StrDec (name,None))` +
   `Names.installStructName` + `Names.insertStruct (ns, mid)`.
2. Open/continue the session: if `open_scope` already holds this `name`, reuse its
   `installs` list; otherwise install the child's consts bare via `installConstName`, record
   them, and set `open_scope := Some (name, installs)`.
3. Recurse: `install1 ~scope_installs:(Some body_installs) child_ns body`.
4. `Names.installComponents (mid, child_ns)` to persist the structure's members.

### `reset ()` (`:890`)
Clears the singletons — `open_scope := None`, `current_group_ns := Names.newNamespace ()`,
plus `required_files`, `Options.tbl`, `Frontend…reset ()`. (This is the bug-class from the
`pi1` shadowing fix: process-wide state must be cleared between runs/tests.)

## 5. Use-site resolution during reconstruction — `src/Recon/ReconTerm.ml`

When a *term* mentions an identifier, reconstruction resolves it through a chain of "finders",
each of which either resolves or delegates to the next (`fc` = failure continuation):

- `findConst ?shortest fc (g_, qid, r)` (`:542`) — calls `Names.resolveQid ~shortest qid`;
  on hit, classifies the cid (`ConDec → Const`, `ConDef → Def`, `AbbrevDef → NSDef`).
- `findBVar` (bound var in the local context) → `findConst` (signature constant) →
  `findCSConst` (constraint-domain constant, `:561`) → `findEFVar` (free/existential var,
  `:571`) → `findOmitted` (`_` placeholder).
- Assembled per identifier kind:
  - `findLCID = findBVar (findConst (findCSConst findOmitted))` (`:579`) — lowercase ids.
  - `findUCID = findBVar (findConst (findCSConst (findEFVar findOmitted)))` (`:581`) —
    uppercase ids (may become existential/free variables if unresolved).
  - `findQUID form = findConst ~shortest:(form = Cst.Abs) (findCSConst findOmitted)` (`:584`) —
    the `%val`/`%abs` qualified terms; this is where `qid_form` becomes the `~shortest` flag.

(An analogous, smaller path lives in `Impl.lookup_head` (`:395-403`) used for world/family
resolution, which calls `Names.constLookup` for bare heads and `Names.resolveQid
~shortest:(form = Cst.Abs)` for `Qualified` heads.)

---

## End-to-end summary

```
%scope/%open        %abs/%val/%( )
   │ Cmd.ml            │ Modern.ml
   ▼                   ▼
Cst.Open_ / Scope_   Quid_ …, qid_form=Val|Abs        (Common/Cst/Cst.ml)
   │                   │
   ▼ install1          ▼ reconstruction
Impl.Install:         ReconTerm.findQUID/findUCID/findLCID
  install_condec        └─ findConst ~shortest ──┐
  Open_  → promote bare (installConstName/insertConst)
  Scope_ → child ns + open_scope session         │
  guard  → uninstallConst on session close        ▼
                                          Names.resolveQid ~shortest   (Names_.ml:553)
                                            ├ false → constLookup (bare, shadow-aware)
                                            └ true  → constLookupIn currentGroupNamespace
                                                       else constLookup
```

- **Parse** in `Fronts/Modern`, **data** in `Common/Cst`, **install-time environment mutation**
  in `Fronts/Pal/Impl.ml`, **use-site lookup** in `Recon/ReconTerm.ml`, **the tables and the
  `resolveQid` policy** in `Names/Names_.ml`.
- The whole `%abs` vs `%val` distinction reduces to one boolean (`~shortest`) threaded from
  `qid_form` down into `resolveQid`, which decides between the group-local namespace and the
  global shadow-aware bare table.
