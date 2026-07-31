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

## Reproducing

```bash
dune build tools/curry/curry.exe
./_build/default/tools/curry/curry.exe targets            # the val table
./_build/default/tools/curry/curry.exe locate > docs/curry-sites.txt
./_build/default/tools/curry/curry.exe locate src/Compress   # scoped to one library
./_build/default/tools/curry/curry.exe patch  src/Compress   # apply
```

`patch` applies only `SIG`/`DEF`/`DEFFUN`/`CALL` edits; `ESCALATE` and `VALUEUSE`
are report-only and never written. `VALUEUSE` is advisory and noisy — it matches
on name, so it also flags unrelated values that happen to share a target's name
(`I.shift`, ppx-derived `eq`).
