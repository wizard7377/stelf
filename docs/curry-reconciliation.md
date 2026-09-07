# Phase A gate: reconciling `tools/curry` against an independent scan

The currying refactor's safety argument depends on the locator finding the right
sites. To check it, the Parsetree tool's output was diffed against an
independent, regex-and-paren-matching scan written separately. The gate is *not*
a percentage agreement — the two measure different sets — but a category-by-
category account of every difference.

## Result

| | scan | `tools/curry` |
|---|---|---|
| target names (arity 2–3) | 315 | 316 |
| acted-on call sites (unique `file:line`) | 3,103 | 2,896 |
| in both | — | **2,820** |
| scan only (tool declines) | — | 283 |
| tool only (scan missed) | — | 76 |

**The tool is more correct than the scan in every category examined.**

### Scan-only: 283 sites the tool declines

- **209 (74%) — multi-arity names.** `sub`, `update`, `check`, `match_`,
  `matchBlock`, `sProgInstall`, `dec` are each declared with two different
  arities across different signatures. The scan accepted a site if the tuple
  length matched *any* of them; the tool refuses the name outright. The tool is
  right — a name-keyed rewrite cannot disambiguate these without types.
- **~43 — target function passed as a value.** Overwhelmingly
  `Timers.time Timers.printing expToString (IntSyn.Null, v_)`, where the tuple
  belongs to `Timers.time`, not to `expToString`. The scan matched on the name
  and claimed the tuple; the tool correctly sees the callee is `Timers.time`.
  **These are real breakage** once the inner function is curried — see residue
  below.
- ~31 — multi-line calls the diff helper could not attribute to a name.

### Tool-only: 76 sites the scan missed

- **46 — `Parsing.error (r, "…`:' or `=', found " ^ …)`.** The scan blanked
  string literals for *locating* but then split the argument on the raw text, so
  commas inside string literals inflated the arity and it declined. The tool
  parses, so string contents cannot affect it. This is the class of error that
  motivated using a real parser.
- ~30 — multi-line applications and `f (a, b) c` forms (tupled first argument
  followed by further arguments), which the scan attributed to a different line.

## Bugs this gate caught

1. **16 edits targeting `basis/`.** `Int.compare`, `List.drop` and
   `String.extract` are declared tuple-style in the `basis/` submodule, which is
   permanently out of scope, but the same names are also declared in project
   signatures. Fixed by declining any call whose first qualifier is a `basis/lib`
   module name, read from the submodule at runtime so it stays in sync.
   (273 sites now declined on this ground.)
2. **`non_overlapping` compared byte offsets across different files**, so it
   discarded 2,787 of 3,884 edits. Fixed by grouping per file; genuine nested-call
   overlaps are now 115, deferred to a second pass.

## Known residue for Phase C

- **54 `Timers.time <target> (a, b)` sites.** Cannot be rewritten mechanically;
  each becomes a type error once the inner function is curried, and each needs a
  hand decision (`Timers.time t (f a) b` vs. a `fun` wrapper).
- **126 ESCALATE sites** — more than one effectful tuple component, so currying
  would silently swap one unspecified evaluation order for another.
- **`src/Table/Table.mli` does not parse as an interface** — it contains
  structure code (`module X = F(…)` with `let` bindings). `Table` is absent from
  `src/Table/dune`'s `(modules …)`, so the file is dead and uncompiled.
  Pre-existing, unrelated to this refactor, left alone.

## Phase D: the single-arity names are now exhausted

Two further rounds (96 tool edits) cleared the last 18 single-arity targets —
`abstractSub'`, `addSolution`, `checkType`, `coninst`, `convDec`, `convFor`,
`conv_dec`, `formatFun`, `funToString`, `mapp`, `memberCtx`, `piDepend`, `query`,
`querytabled`, `solve`, `strinst`, `theoremDecToConDec`, `theoremDecToModeSpine`.
`curry locate` now reports `auto=0`; every remaining decline is one of the eight
dual-arity names (`check`, `condec`, `dec`, `matchBlock`, `match_`,
`sProgInstall`, `sub`, `update`), which a name-keyed rewrite cannot disambiguate
without types.

**16 hand fixes were needed**, in the shape the tool structurally cannot see: a
definition already curried into `let f a b = match a, b with` (the output of an
earlier round, or of `defun`) rather than destructuring the tuple in the
parameter. The tool rewrites the `val` and the call sites and leaves the
definition, so the type checker names each one. The fix is uniform —
`let f a1 a2 b = match (a1, a2), b with` — and was applied to `convDec`,
`piDepend`, `convFor`, `solve`, `checkType`, `addSolution`, `formatFun`,
`funToString`, `abstractSub'` and `query`.

Two other residue shapes appeared, both predicted by the `Longident.last` risk
noted above:

- **Local shadows of a target name.** `Tomega.ml`'s own `convDec`,
  `AbstractTabled.ml`'s and `MtpAbstract.ml`'s own `piDepend` are distinct
  functions that happen to share a target's name, so their call sites were
  rewritten too. All three have the same tupled shape, so currying them is
  consistent rather than a repair — but the tool could equally have hit a
  function where it was not.
- **Call sites passing a tuple-valued *variable*.** `E.Short.mapp mId mS'`,
  `ThmSyn.theoremDecToConDec tdec_ r` and `AbsMachineSbt.solve` under
  `TimeLimit.timeLimit` are declined as "argument is not a literal tuple". Each
  was fixed by destructuring at the binding (`let mode_, mname = …`) rather than
  by projecting at the call.

## Phase E: the width->=4 names, by hand

Phase E was deferred with the note that width >= 4 "wants labelled arguments or
records, which is design work, not a mechanical pass". That was half right. The
design question turned out to be small; what actually stopped the tool was name
collision. `collect_targets` keys on `Longident.last`, and every one of these
names is also borne by an unrelated function of a different arity somewhere in
the tree -- `root` occurs 61 times in 22 files, `solve` 174 in 46, `update` 130
in 29, `matchSig` in seven modules at four arities. So this phase was done by
hand, one name at a time.

Measured by widening the pass's window to `[4, 99]` and running
`refactor curry targets`, the set was **23 names over 26 signature sites**. The
tool was used only to measure; every edit here is manual.

### The criterion

A tuple stays a tuple when it **has a name** -- it is spelled as a type alias, or
appears as a type elsewhere in the signature. It is an argument list, and
curries, when it is spelled inline in that one `val` and nowhere else.

Applied honestly the keep bucket is one row, not the several the width suggested.

### Verdicts

| name | site | verdict |
|---|---|---|
| `deduce` | Terminate/CHECKING.ml | curried 4 |
| `installSig` / `installStruct` | Modules/MODSYN.ml | curried 4 / 5; tupled `action` callback kept |
| `defn` `tydefn` `abbrev` `tyabbrev` | Compress/SGN.ml | curried 5; follows `tycondec` in the same signature |
| `newEVarTC` | IntSyn/TOMEGA.ml | curried 4; follows sibling `newEVar` |
| `apxToClass` | IntSyn/APPROX.ml | curried 4 |
| `apxToExact` | IntSyn/APPROX.ml | curried 4; `IntSyn.eclo` kept |
| `invertible` | IntSyn/UNIFY.ml | curried 4; `IntSyn.eclo` kept |
| `invertSub` | IntSyn/UNIFY.ml | curried 4 |
| `searchEx` / `searchAll` | M2/SEARCH.ml | curried 4; `exp * sub` kept |
| `mroot` | Frontend/RECONMODE.ml (`Short`) | curried 4; `mspine` kept |
| `rdecl` | Frontend/RECONTHM.ml | curried 4 |
| `rdecl` | Common/Cst/CST.ml | curried 4 -- see below |
| `abstractSub` | Meta/MTPABSTRACT.ml | curried 5; `(dctx * tag ctx)` kept |
| `root` | Paths/PATHS.ml | curried 5; follows siblings `bind`, `app` |
| `matchSig` | Compile/SUBTREE.ml | curried 4; `eclo` and tupled callback kept |
| `solve` | Opsem/PTRECON.ml | curried 5; `(goal, sub)` split to match ABSMACHINE |
| `callCheck` | MEMOTABLE.ml + SWSUBTREE.ml | curried 6 |
| `insertIntoTree` | MEMOTABLE.ml + SWSUBTREE.ml | curried 7 |
| `update` | Table/SPARSEARRAY2.ml | **kept tupled** |

`Cst.rdecl` was planned as a keep and the plan was wrong. `type rdecl =
predicate * order * order * callpats` sits beside it and the implementation is
the identity on that type, which is the coupling argument for keeping it. But
`predicate`, `tdecl`, `tableddecl`, `keepTabledecl`, `prove` and `establish` in
the same module have exactly that shape -- `type tdecl = order * callpats` /
`let tdecl order callpats = (order, callpats)` -- and every one is already
curried. Family consistency won.

`SparseArray2.update` is the only keep, and not because its tuple is a value:
it is a plain argument list. Its sibling `sub` is arity 3, so it sits in the
dual-arity set this document already defers, and callers use the two in one
expression -- `Array2.update (a, i, j, Array2.sub (a, i, j) + v)` at
CsIneqField.ml:196. Splitting that pair reads worse than leaving it. If `sub` is
ever brought into scope, both move together.

One name, two verdicts: `rdecl` is the worked example of why name-keying failed.
ReconThm's destructures pair components and joins their regions; Cst's is the
identity on its own type alias. A `Longident.last` rewrite sees one name.

### The compiler as the call-site oracle, and its two blind spots

Grep inherits exactly the collision problem that stopped the tool, so it was not
the worklist. Per name: edit the `val` and the definition, run
`dune build @check`, and the type errors *are* the complete call-site list --
`f (a,b,c,d)` cannot typecheck against `f : a -> b -> c -> d -> e` by accident,
and warning 5 is fatal in these libraries, so under-application is caught too.

Two sites the compiler could not have caught, both found by grepping for
un-applied uses:

- **`Obj.magic`.** MtpSplitting.ml:370 applies `MTPAbstract.abstractSub` through
  `Obj.magic`, which erases the arity. Left tupled it would have compiled
  cleanly and then read the fields of a partial-application closure as if it
  were a 5-tuple. A tree-wide sweep for `Obj.magic` applied to any of the 23
  names finds no other site.
- **Higher-order wrappers.** M2/Filling.ml's local `delay search params ()`
  forwarded the arguments as a tuple, and Solve.ml's three `PtRecon.solve` calls
  go through `Timers.time`. `Timers.time` is polymorphic in the argument, so a
  curried callee still typechecks -- it just times a partial application. Both
  use the `Timers.time c (fun () -> ...) ()` form the earlier round already
  established at Solve.ml:287.

### Residue

`refactor curry targets` over `[4, 99]` now reports one name, `update`, the
deliberate keep.

Deliberately not touched, and still tupled at arity >= 4: internal helpers that
back nothing exported -- `AbstractTabled.ml:705` `abstractSub` (10 parameters),
`MetaAbstract.ml:334` (7), `MtpAbstract.ml:263` (5), `Abstract.ml:266` (4),
`Uniquesearch.ml:161` `solve` (6), `MtpSearch.ml:158` (5), `Psearch.ml:159` (5),
`M2/Search.ml:92` (4), `Cover_.ml:437` `matchSig` (5). Also `Unify.ml`'s
`invertExp`, which shares a `let rec ... and` chain with the curried `invertSub`
and is now visibly inconsistent with it, and `Ptrecon.ml:113`'s `solve'`, whose
`(goal, sub)` pair is the match scrutinee.

No labelled arguments were introduced. `callCheck`'s three adjacent `IntSyn.dctx`
is the one place they would genuinely help; the definitions already name them
`dAVars` / `dEVars` / `g`, every call site passes them in that order, and adding
labels is a redesign rather than the currying that was asked for.

## Reproducing

```bash
dune build tools/refactor/refactor.exe
./_build/default/tools/refactor/refactor.exe curry targets            # the val table
./_build/default/tools/refactor/refactor.exe curry locate > docs/curry-sites.txt
./_build/default/tools/refactor/refactor.exe curry locate src/Compress   # scoped
./_build/default/tools/refactor/refactor.exe curry patch  src/Compress   # apply
```

`patch` applies only `SIG`/`DEF`/`DEFFUN`/`CALL` edits; `ESCALATE` and `VALUEUSE`
are report-only and never written. `VALUEUSE` is advisory and noisy — it matches
on name, so it also flags unrelated values that happen to share a target's name
(`I.shift`, ppx-derived `eq`).
