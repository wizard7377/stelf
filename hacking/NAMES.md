# How Names Are Handled in the Original Twelf (SML)

## Context

This document is a reference explanation, not a code change. It traces how
Twelf — the SML codebase under `twelf/src/` that `stelf` is porting — manages
identifiers from raw input bytes through internal LF terms and back out as
pretty-printed text. The aim is to give a faithful, citable picture of the
*original* design so that the OCaml port (and anyone reading it later) has a
single reference for why the new `Names`/`Cst`/`IntSyn` layers are shaped the
way they are.

The headline observation: **terms themselves carry almost no name
information**. A constant is an `int` (`cid`), a bound variable is a de Bruijn
`int`, an EVar is a `ref` cell. All strings — the names a user reads or
types — live in a parallel `Names` structure indexed by those ints. Parsing,
elaboration, fixity, and printing all consult that side store; the LF kernel
never sees a string.

---

## 1. Where names are stored

There are three physically distinct storage layers.

### 1.1 In `IntSyn` — names attached to declarations only

`twelf/src/lambda/intsyn.sig` and `intsyn.fun` define the LF core. The
relevant types:

- `type cid = int`, `type mid = int`, `type csid = int`  (intsyn.sig:8–10) —
  constant id, module/structure id, constraint-system id. All three are
  bare integers used as array indices into `IntSyn`'s signature table.
- `Head = BVar of int | Const of cid | …`  (intsyn.sig:60–67). A bound
  variable is *only* its de Bruijn index; a constant is *only* its `cid`.
  Neither carries a string.
- `Dec = Dec of string option * Exp | BDec … | ADec … | NDec of string option`
  (intsyn.sig:86–91). Declarations in a context optionally carry a name
  *hint* (e.g. the `x` in `[x:nat] …`). `NONE` means "anonymous, invent one
  at print time."
- `ConDec` (intsyn.fun:147–171): every constant declaration variant
  (`ConDec`, `ConDef`, `AbbrevDef`, `BlockDec`, `BlockDef`, `SkoDec`) starts
  with `string * mid option * int * …`. The string is the constant's name;
  the `mid option` is its parent module. Accessor: `conDecName` at
  intsyn.fun:229.
- `EVar` (intsyn.fun:71) carries an `Exp option ref` but **no name field** —
  EVars are identified by reference equality.
- `FVar of name * Exp * Sub` (intsyn.fun:89) is the one exception in the
  term language: free variables embed their string directly, because they
  are introduced by the parser (uppercase identifiers in queries) and
  never need a fresh name invented for them.

So inside `IntSyn`, the only names that exist are: the constant name in
`ConDec`, the optional name hint in `Dec`, and the embedded string in `FVar`.
Everything else is anonymous and must be resolved through the `Names`
module.

### 1.2 In `Names` — the bidirectional registry

`twelf/src/names/names.fun` holds the rest. It is a collection of mutable
tables keyed by either strings or `cid`/`mid`:

| Table | Type | Purpose |
|-------|------|---------|
| `topNamespace` (names.fun:220) | `cid HashTable.Table` | unqualified `string → cid` |
| `topStructNamespace` (:236) | `mid HashTable.Table` | unqualified `string → mid` |
| `shadowArray` (:210) | `cid option Array.array` | per-cid: previous cid this one shadowed |
| `structShadowArray` (:229) | `mid option Array.array` | same for structures |
| `fixityArray` (:213) | `Fixity.fixity Array.array` | per-cid fixity (default `Nonfix`) |
| `namePrefArray` (:216) | `(string list * string list) option Array.array` | per-cid name preferences (`%name` decls) |
| `componentsArray` (:232) | `namespace Array.array` | per-mid namespace (structure contents) |
| `varTable` (:616) | `varEntry StringTree.Table` | local: name → EVar/FVar during one decl |
| `evarList` (:629) | `(Exp * string) list ref` | local: EVar/AVar → name |
| `indexTable` (:662) | `int StringTree.Table` | local: base name → next suffix |

The first seven persist for the life of the signature; the last three are
local to a single declaration or query and reset by `varReset` (:681).

`type namespace = mid StringTree.Table * cid StringTree.Table` (names.sig:53):
a pair of red-black trees, one for sub-structures, one for constants. Each
module owns one; `topNamespace`/`topStructNamespace` are the global root.

### 1.3 Why two stores instead of one

The README in `twelf/src/names/` calls the central invariant out: the
forward map (`name → cid`) and the reverse map (`cid → name`, recoverable
via `ConDec.name` plus the parent `mid`) must stay consistent under
shadowing and module operations. Keeping the *name string* on the
declaration (`ConDec`) and the *name lookup tables* in `Names` is what makes
that consistency cheap: re-installing the same `ConDec` after an undo
restores its canonical name automatically, and shadowing only needs to
patch the side tables, not rewrite any term.

---

## 2. How names translate to internal ids

The lifecycle from raw text to a resolved `cid` runs through three layers:
the lexer, the parser (which leaves strings in the CST), and the
reconstruction phase (where strings finally become `cid`s).

### 2.1 Lexer — bytes to tokens

`twelf/src/frontend/lexer.fun` produces `ID(IdCase, string)` tokens. The
`IdCase` discriminator (lexer.sig:11–14) is `Upper | Lower | Quoted`. The
case matters semantically — uppercase identifiers in terms become EVars by
default; lowercase ones look up constants — so it has to be preserved into
the CST.

Qualified identifiers (`Mod.foo`) are handled with a one-character
lookahead in `lexContinueQualId` (lexer.fun:323–330): a `.` between two
identifier characters becomes the special token `PATHSEP`; otherwise it
stays a plain `DOT` (for `a. b` syntax). This decision is purely local —
the lexer never consults the name tables.

Pragma keywords (`%name`, `%infix`, `%prefix`, `%postfix`, …) are matched
in `lexPragmaKey` (lexer.fun:229–265).

### 2.2 Parser — CST nodes still carry strings

`parse-term.fun:189–197` defines `parseQualId'`, which collects an
`(ids : string list, name : string)` pair and wraps it as
`Names.Qid (ids, name)`. The constructor

```sml
datatype Qid = Qid of string list * string
```

(names.sig:47, names.fun:153) is the canonical "qualified identifier" used
by every layer above the lexer; `qidToString` and `stringToQid`
(names.fun:155, 164) round-trip the dotted form.

`parseExp'` (parse-term.fun:309–328) wraps the id in a CST node tagged by
case — `lcid`, `ucid`, or `quid`. **At this point the parser does call
`Names.fixityLookup`** (parse-term.fun:319–327) on the `Qid` to drive
operator-precedence parsing. That is the only name-table contact the
parser has, and it is read-only — the identifier remains a string in the
CST. The result is a CST tree whose leaves are unresolved `Qid`s, plus
fixity hints used during shift/reduce.

Fixity, name-preference, and constant declarations are likewise parsed
into `Qid`-bearing records by `parse-fixity.fun:42–75` and
`parse-condec.fun:86–89`; nothing is registered with `Names` yet.

### 2.3 Reconstruction — `Qid` becomes `cid`

`twelf/src/frontend/recon-term.fun` performs the resolution. The pivotal
function is `findConst` (:375–387):

```sml
fun findConst fc (G, qid, r) =
    (case Names.constLookup qid
       of NONE => fc (G, qid, r)
        | SOME cid => (case IntSyn.sgnLookup cid of …))
```

`Names.constLookup` (names.fun:392) dispatches on the `Qid`'s path
component:

- empty path → `HashTable.lookup topNamespace id`;
- non-empty path → `findTopStruct ids` to walk module structures, then look
  the unqualified id up in that module's `constComps` (names.fun:317).

The fallback `fc` differs by `IdCase`:

- `lcid` → try bound variable (`findBVar`), then constant, then the
  constraint-system (`CSManager`), else error.
- `ucid` → try bound variable, then `CSManager`, else **create an FVar**
  with the original string (recon-term.fun:191–201, using `fvarTable` and
  `fvarApxTable` to keep approximate types coherent across uses).
- `quid` → strict constant lookup only.

Free occurrences of an uppercase identifier in a query produce an EVar
through `getEVar` (recon-term.fun:177–189), which checks
`Names.getEVarOpt name`; on a miss it allocates a fresh `IntSyn.newEVar`
and records the name with `Names.addEVar (X, name)` (names.fun:687) so the
*next* occurrence in the same query maps to the same EVar.

The result: every string in the CST is replaced either by a resolved
`Const cid`, a `BVar k` (with the matching string flowing into the
context's `Dec`), an `FVar (name, …)`, or by an EVar tracked through
`evarList` under the user's chosen name.

### 2.4 Installing a new constant

When the user writes `c : A`, `recon-condec.fun:58–116` runs the full
reconstruction (`Names.varReset`, `ExtSyn.recon`,
`Abstract.abstractDecImp`, `Names.nameConDec`). The cid itself is
allocated by `IntSyn.sgnAdd` (in the driver `twelf.fun`); the side effect
that makes the new name visible globally is `Names.installConstName`
(names.fun:249), which does `topInsert (id, cid)` and, if a previous cid
already bound that name, records the displaced cid in
`shadowArray.[cid] <- SOME old`. Structures go through the analogous
`installStructName` (:274).

`Names.installFixity` (:479) and `Names.installNamePref` (:518) are
triggered by `twelf.fun:755–775` for `%infix`/`%prefix`/`%postfix` and
`%name` pragmas, after `Names.constLookup` has converted the pragma's
`Qid` to a `cid`.

---

## 3. How pretty printing transfers names back

The printer is in `twelf/src/print/print.fun`. The entry point most callers
use is `formatExp : dctx * Exp -> Formatter.format` (:939). The pipeline is
the mirror image of reconstruction.

### 3.1 Heads

`fmtCon` (print.fun:264–292) handles atomic heads:

```sml
fmtCon (G, I.BVar n)    = Str0 (Symbol.bvar (Names.bvarName (G, n)))
fmtCon (G, I.Const cid) = fmtConstPath (Symbol.const, Names.constQid cid)
fmtCon (G, I.FVar (name, _, _)) = Str0 (Symbol.fvar name)
```

- `Names.bvarName (G, k)` (names.fun:801) reads the `Dec` at depth `k` from
  the context and extracts its `SOME(name)` field. If the field is `NONE`
  the printer raises `Unprintable`: the contract is that *the context
  passed to `formatExp` has already been name-annotated* (see §3.3).
- `Names.constQid` (:456) reconstructs the dotted form. It walks the
  parent-`mid` chain via `structPath` (:430) starting from the `ConDec`'s
  own `mid option`. Then it cross-checks with `constLookup`: if
  re-resolving the path doesn't return the same `cid`, the name is
  shadowed, and `maybeShadow` (:440) wraps the leading segment in `%…%`
  so the output is unambiguous.

EVars use `fmtEVar` (print.fun:58–62), which calls `Names.evarName (G, X)`
(names.fun:783). That function looks `X` up in `evarList` by reference; on
miss, it calls `newEVarName` (:761), which picks a base name via
`namePrefOf` (:564) — driven by `namePrefArray[head_cid]` if the EVar's
type has a constant head — and finishes with `tryNextName` (:727) to add
a fresh integer suffix.

### 3.2 Fixity-driven application layout

`fixityCon` (print.fun:189–194) reads `Names.getFixity cid` (which is just
`Array.sub (fixityArray, cid)` at names.fun:490). Based on
`Fixity.Infix (prec, assoc) | Prefix prec | Postfix prec | Nonfix`,
`opargs` (:506–513) dispatches to:

- `opargsExplicit` (:477–504) — elides the right number of implicit
  arguments (so an `Infix` with two implicits prints `M + N`, not
  `+ _ _ M N`);
- `opargsImplicit` / `opargsImplicitInfix` (:449 and friends) — used when
  `!implicit` is set, which shows every argument verbatim.

Precedence comparisons use `Fixity.less`/`leq` (names.fun:51–60) so
sub-expressions get parenthesized exactly when their precedence is lower
than the surrounding context's.

### 3.3 Threading names through binders

When `fmtExpW` (print.fun:743–761) walks under a binder, it must produce
a `Dec` whose `string option` is `SOME` *and* unique in the current
context. The relevant calls are `Names.decLUName` for the local-extent
case (under `λ` and quantifier bodies) and `Names.decEName`/`decUName`
for top-level implicit/explicit parameters.

`decName'` (names.fun:816, exported as `decName`/`decEName`/`decUName`/
`decLUName` at :865–868) does the work:

1. If the `Dec` already has `SOME name`, check `varDefined name orelse
   conDefined name orelse ctxDefined (G, name)`. If any is true, the name
   would shadow something visible; replace it with
   `tryNextName (G, baseOf name)` (a fresh `name<n>`). Otherwise keep it.
2. If the `Dec` is anonymous (`NONE`), call `findName (G, namePrefOf (role, V),
   extent role)` to pick a base from the type's `%name` preference list
   (defaulting to `"X"` for existentials, `"x"` for universals — :549–557)
   and add a suffix until it is fresh.

`ctxName` / `ctxLUName` (:876–893) recursively annotate every `Dec` in a
context, and `pisEName` / `defEName` (:899–947) do the same for the
implicit-`Π` prefix of a `ConDec`. The result is that by the time
`formatExp` recurses into a binder, the context `G` it sees has a
`SOME name` for every depth, no name collides with a visible constant or
EVar, and `bvarName` can simply look the string up.

Shadowing of variables is prevented entirely; shadowing of constants is
made explicit with the `%name%` wrapper described above.

### 3.4 Shadow round-trip

`reset` (names.fun:311) clears the global tables; `resetFrom (mark,
markStruct)` (:298) is the incremental version used when reverting a file
load. It calls `uninstallConst` (:259), which checks the `shadowArray` and
restores any previous binding before clearing its own slot — so after a
reload the name tables and the `ConDec` strings remain consistent
without any term being rewritten.

---

## 4. Name management & the metadata attached to a name

Conceptually, "a name" in Twelf is a `Qid`. The metadata fanout is:

| Per `cid` | Source | Lives in |
|-----------|--------|----------|
| canonical string | `ConDec` first field | `IntSyn.sgnLookup cid |> conDecName` |
| parent `mid option` | `ConDec` second field | same |
| number of implicit args | `ConDec` third field | same |
| fixity | `%infix`/`%prefix`/`%postfix` | `fixityArray[cid]` |
| name preferences (`ePref`, `uPref`) | `%name` | `namePrefArray[cid]` |
| shadowed predecessor cid | install-time | `shadowArray[cid]` |

| Per `mid` | Source | Lives in |
|-----------|--------|----------|
| structure name | `StrDec` | `IntSyn.sgnStructLookup mid` |
| parent `mid option` | `StrDec` | same |
| components (namespace) | structure body | `componentsArray[mid]` |
| shadowed predecessor mid | install-time | `structShadowArray[mid]` |

| Per local variable | Source | Lives in |
|--------------------|--------|----------|
| optional name hint | `Dec`/`BDec`/`ADec`/`NDec` | the context itself |
| de Bruijn position | term structure | `BVar k` |

| Per EVar/FVar | Source | Lives in |
|---------------|--------|----------|
| EVar identity | `IntSyn.newEVar` | the `ref` cell |
| EVar name | first occurrence in input or invented at print time | `evarList` + `varTable` |
| FVar name | parser | embedded in `FVar` constructor |

The "local" tables (`varTable`, `evarList`, `indexTable`) are reset by
`varReset G` (:681) at the start of every reconstruction job and every
print job for an isolated expression. They scope precisely one decl or
one query, so EVar naming choices never leak between declarations.

Helper predicates for collision avoidance:

- `varDefined name` (:698) — is `name` already in `varTable`?
- `conDefined name` (:704) — does `Names.constLookup (Qid (nil, name))`
  succeed?
- `ctxDefined (G, name)` (:710) — is `name` already the hint of some `Dec`
  in `G`?
- `tryNextName (G, base)` (:727) — loop appending `Int.toString
  (nextIndex base)` until none of the above hold.

These three predicates are the closest thing Twelf has to a unified
"is this name taken?" check; all naming functions go through them.

Skolem constants generated during proof search get their names via
`skonstName name = tryNextName (IntSyn.Null, name)` (:953) — the null
context is fine because Skolems live at the top level of the signature.

---

## 5. Fixity

### 5.1 The `Fixity` substructure

Declared in `names.sig:5–33` and defined in `names.fun:31–82`:

```sml
datatype associativity = Left | Right | None
datatype precedence    = Strength of int
datatype fixity =
    Nonfix
  | Infix   of precedence * associativity
  | Prefix  of precedence
  | Postfix of precedence
```

`maxPrec = Strength 9999`, `minPrec = Strength 0` (:44, :46). Comparison
and arithmetic (`less`, `leq`, `compare`, `inc`, `dec`, `prec`) operate
on `precedence` so the printer's "do I need parens?" check is a single
integer comparison.

`precToIntAsc` (:63) flips the encoding for export to formats where lower
numbers conventionally mean "binds tighter."

### 5.2 Storage

`fixityArray : Fixity.fixity Array.array` (:213), indexed by `cid`,
initialised to `Nonfix`. `installFixity (cid, fixity)` (:479) writes a
slot; `getFixity cid` (:490) reads it; `fixityLookup qid` (:496) is the
`Qid`-keyed convenience that does `constLookup` first.

`checkFixity` (:122), via `checkArgNumber` (:108–115), verifies that the
constant's type has at least the required number of *explicit* arguments
(2 for infix, 1 for prefix/postfix). Implicit `Π`-bound parameters are
discounted because the printer hides them by default.

### 5.3 Fixity at parse time

The fixity table is consulted by `parseExp'` (parse-term.fun:319–327)
*every time* an identifier is parsed, to choose between shift and reduce
in the operator-precedence loop. This is why fixity declarations have
file-order significance in Twelf source: a `%infix` introduced *after* a
use of the operator does not apply to that earlier use.

### 5.4 Fixity at print time

As described in §3.2, the printer dispatches on `Fixity.fixity` to decide
both the *layout* (operator between, before, or after its arguments) and
the *parenthesisation* (sub-expression precedence vs. context
precedence). Together with `%name`-driven variable choice and shadowing
markers, this is everything the printer needs.

---

## 6. All call sites of `Names` and other name-managing modules

### 6.1 Producers (mutators of `Names`)

| Caller | What it installs | `Names` entry point |
|--------|------------------|---------------------|
| `recon-condec.fun` (after `IntSyn.sgnAdd`) | constant name, implicit count | `installConstName`, `nameConDec` |
| `recon-module.fun` | structure name, components | `installStructName`, `installComponents` |
| `twelf.fun:755` | fixity | `installFixity` |
| `twelf.fun:769` | name preference | `installNamePref` |
| File loader / unload | bulk reset | `reset`, `resetFrom`, `uninstallConst`, `uninstallStruct` |

### 6.2 Consumers (readers of `Names`)

| Caller | What it asks | `Names` entry point |
|--------|--------------|---------------------|
| Lexer | (none — lexer is name-table free) | — |
| `parse-term.fun:319` | fixity for shunting-yard | `fixityLookup` |
| `recon-term.fun:375` | `Qid → cid` | `constLookup` |
| `recon-term.fun:177` | EVar identity by name | `getEVarOpt`, `addEVar` |
| `recon-term.fun` (FVar path) | approximate type cache | `varReset` (clears) |
| `recon-module.fun:30` | `Qid → mid` | `structLookup`, `structComps` |
| `print.fun:189` | per-cid fixity | `getFixity` |
| `print.fun:265` | canonical `cid → Qid` | `constQid` |
| `print.fun:265` | bound-var name in context | `bvarName` |
| `print.fun:59` | EVar name | `evarName` |
| `print.fun:743` | name a binder | `decLUName`, `decEName`, `decUName` |
| Solver / queries | named EVars for goals | `namedEVars`, `evarCnstr` |
| Meta-prover / Skolem | fresh constant names | `skonstName` |
| Coverage, abstraction, theorem | naming implicits before printing | `nameConDec`, `pisEName`, `ctxName` |

### 6.3 Other modules that participate in name management

- **`IntSyn` (`twelf/src/lambda/intsyn.{sig,fun}`)** — owns the canonical
  string for every `ConDec`, the parent `mid`, and the bound-variable
  name hints on `Dec`/`BDec`/`ADec`/`NDec`. Without `IntSyn` the
  `Names` tables would have nothing to refer to.
- **`Paths` (`twelf/src/paths/`)** — pairs each name occurrence with a
  source `region`, used for error messages keyed off the original text;
  not a name table per se but every `Qid` passed through reconstruction
  carries a paired `region`.
- **`Origins` (`twelf/src/origins/`)** — maps `cid → origin file/region`
  so that "where was `nat` declared?" queries can be answered without
  another table on `Names`.
- **`CSManager` (`twelf/src/solvers/`)** — registers names for
  foreign/constraint-system constants. `findConst`'s lookup chain calls
  it after `Names.constLookup` misses, so e.g. integer literals like
  `0`, `1`, … become `CSConst` heads instead of FVars.
- **`ModSyn`/`Modules`** — internal representation of structures and
  signatures; collaborates with `Names` whenever a structure is
  instantiated, copied, or opened (each operation may install or alias
  components).
- **`Print` (`twelf/src/print/`)** — the *only* consumer that needs all
  three categories of name data at once (constant strings, fixities,
  context-annotated binders), which is why it lives just above
  `Names` in the dependency graph.
- **`Frontend_` / `Twelf_` (`twelf/src/frontend/twelf.fun`)** — the
  driver that orders all of the above: parse → reconstruct →
  `IntSyn.sgnAdd` → `Names.installConstName` → optional `installFixity`/
  `installNamePref` → print confirmation.

---

## Verification

This is an explanatory document, not a code change, so "verification" is
about checking faithfulness rather than running tests:

1. Cross-check the signatures cited:
   `rg -n 'installConstName|constLookup|installFixity|decLUName|evarName' twelf/src/names/names.{sig,fun}`
2. Confirm the lifecycle by tracing one identifier from input to print:
   parse `c : nat -> nat.` with `dune exec bin/main.exe`, observe the
   resulting `cid`, then pretty-print it back — the round-trip should
   exercise `installConstName`, `constLookup`, `constQid`, and the
   default-`Nonfix` path through `getFixity`.
3. Sanity-check shadowing by declaring two constants with the same name
   in nested structures and observing the `%c%` marker emitted by
   `maybeShadow` (names.fun:440).
4. Re-read the cited line numbers in the order they appear in §1–§5; any
   drift between this document and the source is a documentation bug.

---

## Critical files

- `twelf/src/lambda/intsyn.sig`, `intsyn.fun` — `cid`/`mid`/`Head`/`Dec`/`ConDec`
- `twelf/src/names/names.sig`, `names.fun` — every table and helper
- `twelf/src/frontend/lexer.fun` — tokenisation + qualified-id lookahead
- `twelf/src/frontend/parse-term.fun`, `parse-fixity.fun`, `parse-condec.fun`,
  `parse-module.fun` — CST construction with `Qid`
- `twelf/src/frontend/recon-term.fun`, `recon-condec.fun`, `recon-module.fun`
  — `Qid → cid`/`mid` resolution, EVar/FVar creation
- `twelf/src/frontend/twelf.fun` — driver: orders `IntSyn.sgnAdd` and
  `Names.install*` calls
- `twelf/src/print/print.fun` — consumer of fixity, names, and binder
  annotations
- Adjacent participants: `twelf/src/paths/`, `twelf/src/origins/`,
  `twelf/src/solvers/cs-manager*`, `twelf/src/modules/`
