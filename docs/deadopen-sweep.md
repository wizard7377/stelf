# Dead `open!` sweep, and the warning-66 gate

The old-style libraries carried a 40–60 line `open!` prelude copy-pasted into
every `.ml` and `.mli` — 15,135 lines in `src/` — a transliteration of the SML
`structure` bindings the port started from. Most of it was dead.

## Result

| | |
|---|---|
| `open!` lines in `src/` before | 15,135 |
| deleted as unused | **12,909** (85%) |
| remaining | 2,226 |
| files touched | 519 |
| build errors caused | **0** |

Nothing was reverted and no site needed a hand fix. Five Alcotest suites and the
STELF cram tests are identical to baseline.

## Detection: the compiler, not merlin

`open!` exists to suppress warning 33, so its own unused-warning is **66**
(`unused-open-bang`); enabling 33 would flag nothing.

The plan reached for `ocamlmerlin single errors -- -w +66`, which is right for a
one-file spot-check and wrong for a 15k-line sweep. Merlin typechecks in
isolation, and these libraries carry
`(preprocess (pps ppx_deriving.show ppx_deriving.eq ppx_deriving.ord))` — ppx
output references opened modules, so any divergence in how merlin applies the
preprocessor yields *false dead* verdicts. The sweep instead used the compiler
that also backstops it, in one build rather than ~800 processes.

The edit surface was already narrow. Warning 66 is not exempted from
`dune-workspace`'s `-warn-error` list and the tree built clean, so 66 was
enabled-and-fatal everywhere *except* the 30 libraries whose
`(:standard -w -A+5)` turns it off — `-w` is cumulative and `-A` resets, so a
`+66` in the env `:standard` would be wiped by the later `-A+5`. Those 30 were
therefore the whole of the sweep, and the new-style libraries were already clean.

Two rounds to a fixpoint: 12,723 lines, then 186 more. The second round is a real
cascade, not a re-scan artefact — `open! Intsyn` is marked *used* by
`open! Intsyn.Lambda_`'s path, so deleting the latter makes the former dead.

## Why this needs no scope argument

Warning 66 means *no identifier resolved through this open*. Removal therefore
cannot rebind anything, and independently-flagged opens can be deleted together:
usedness is not coupled, because an open whose path is named through an earlier
one marks that earlier one used and so is never flagged in the same round. That
is why the prelude's `open! X` + `open! X.X_` pairs survive wherever they are
load-bearing. Unlike a rename, `Unbound value` is a complete backstop here.

## The deletion guard

Detection is the compiler; the edit is "delete these lines". A line was deleted
only if it matched `^[ \t]*open!  *[A-Za-z0-9_.']+[ \t]*$` — anything else
(a trailing comment, two opens on one line) would have been reported and left.
**All 12,909 flagged lines matched; 0 were skipped**, so flagged = deleted
exactly.

## Duplicate opens

The 725 exact within-file duplicates the plan counted needed no separate pass:
warning 66 reports the redundant one as unused, so they fell out for free.

21 same-text `open!` lines in 18 files remain. These are not duplicates — a
redundant one in the same scope would have been flagged, since any use resolves
through the innermost. They are the same module opened in two different scopes,
which is exactly what the warning is able to tell apart and a text scan is not.

## The gate

`-w -A+5+66` now stands in all 30 library `dune` files, and warning 66 remains
fatal (`dune-workspace`'s `-warn-error` list does not exempt it). A new dead
`open!` is a build error.

`docs/warning66-baseline.txt` is empty **because nothing survives the gate, not
because nothing was checked** — the two states look identical in a 0-byte file,
and `docs/warning5-baseline.txt` carries the same ambiguity. Every `open!` in the
30 instrumented libraries was measured; the file is the accepted-occurrence list
and it is empty because there is nothing left to accept.

## `open! Formatter__Formatter_`

45 of these survived the sweep. `Formatter__Formatter_` is dune's mangled
internal name for the `formatter` library's `Formatter_` module — a fingerprint
of `wrapped true` being retrofitted onto code written for `wrapped false`. The
public path is `Formatter.Formatter_`.

**34 were rewritten; 11 cannot be.** `Print.Print_` exports a submodule named
`Formatter` (`src/Print/Print_.ml:48`), so in any file whose prelude opens
`Print.Print_` first, the bare name `Formatter` no longer refers to the library
alias and `Formatter.Formatter_` is unbound. The 11 are in `src/Compile/`,
`src/Terminate/` and `src/Prover/`:

```
src/Compile/Cprint.ml      src/Compile/Cprint.mli    src/Compile/Compile_.ml
src/Compile/Subtree.ml     src/Compile/Subtree.mli   src/Terminate/Checking.ml
src/Terminate/Checking.mli src/Terminate/Reduces.ml  src/Terminate/Reduces.mli
src/Prover/Interactive.ml  src/Prover/Prover_.ml
```

Reordering the prelude would unshadow them, but open order is exactly what
warning 66 cannot vouch for, so they keep the mangled name. Two `module Formatter
= Formatter__Formatter_.Formatter` aliases (`src/M2/M2_.ml:52`,
`src/Terminate/Terminate_.ml:32`) fail for the same reason and are also left.

This is a small worked instance of the deferred "qualify the survivors" problem:
the answer is not derivable from the text, only from resolution.

## Out of scope

- `test/Print/dune` sets `(:standard -w -A)`, so its 40 `open!` lines are
  unmeasured, untouched **and ungated** — it is the one place in the tree where a
  new dead `open!` can accumulate silently while everywhere else errors on it.
  That exemption is deliberate, not an oversight: a test executable's prelude is
  not worth a sweep. `test/` and `bin/` have no other `open!` lines.
- `src/Table/Table.mli` is absent from `src/Table/dune`'s `(modules …)`, so it is
  never compiled and produces no data. Left alone, as everywhere else.
- **Qualifying the survivors** is still deferred. Warning 66 says an open
  contributed *nothing*; it cannot disambiguate among survivors with overlapping
  exports resolved last-open-wins, which needs a `Cmt_format` walker over the
  existing `_build/**/*.cmt`.
- Deleting the last `open! X` in a library may leave `X` an unused entry in that
  library's `(libraries …)`. That is not a warning and was not pursued.
