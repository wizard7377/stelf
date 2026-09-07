# `defun` gate: reconciling the locator against an independent scan

`refactor defun` turns `let f = function | (g_, tm, vhs) -> …` into
`let f (g_, tm, vhs) = match tm with …`, hoisting every tuple position whose
pattern is irrefutable in *every* branch and narrowing the scrutinee to the
positions that vary. Arity and type are unchanged — both forms take one tuple —
so no call site moves.

Following `curry-reconciliation.md`, the Parsetree locator was diffed against an
independent regex-and-paren-matching scan written separately. The gate is a
category-by-category account of every difference, not a percentage.

## Result: every live `= function` binding is accounted for

The tool now emits a row for each binding it *skips*, not just each one it acts
on, so the two scans can be compared as sets rather than as totals.

| | count |
|---|---|
| unique `file:line` matching `= function` (regex, tree-wide) | 2,059 |
| − inside a block comment: `IntInf/IntInf_.ml` 53, `Flit/Flit_.ml` 9 | 62 |
| = live bindings | **1,997** |
| tool rows (`DEFUN` + `DEFUN1` + `DECLINE` + `SKIP`) | **1,996** |
| unexplained | **0** |

The single remaining difference is a line anchor, not a site: the scan reports
`src/Fronts/Pal/Impl.ml:447` (`… : 'a list -> Reply.t list =`) where the tool
reports 448 (the `function` keyword on the next line). Same binding, counted once
on each side.

The 62 commented-out hits are the same dead blocks the `letunit` pass ran into:
`Flit_.ml`'s `initTuples` and most of `IntInf_.ml` sit at comment depth 1, so the
parser never sees them. A regex rewriter would have edited them.

## How the 1,996 divide

| bucket | count | |
|---|---|---|
| `DEFUN` | 876 sites (4,629 edits) | rewritten to `= match … with` |
| `DEFUN1` | 33 | one branch, every position irrefutable — no `match` at all |
| `DECLINE` | 102 | mixed `_`/name position; taken up by `--with-any` (below) |
| `SKIP` | 985 | not a tupled `function` in the required shape |

`SKIP` breaks down as 799 "a case pattern is not an unlabelled closed tuple"
(overwhelmingly `function` over a single non-tuple argument, plus the shape where
the first branch is a tuple and a later one is a bare `| _ ->`), 174 "no position
is irrefutable in every branch", and 12 "constrained binding, attributes, or no
cases".

## The two stages, and why they are split on the safety argument

The split is by *what proves the rewrite correct*, not by how many positions move.

**Default stage (`DEFUN`, `DEFUN1`).** A hoisted position binds the same
`Ppat_var` in every branch, or `_` in every branch. This is capture-free by
construction: every branch body that could mention the name already had it bound
to that exact component, and `| g_, Foo g_, vhs` is not legal OCaml, so no branch
can be reading an outer binding. `Core.verify` is therefore a *complete* check
here — shape is all there is, and it reports **0 escalations** tree-wide.

**`--with-any` stage (102 sites).** Some branches bind `_` where others bind the
name. Those `_` branches saw whatever the enclosing scope held, and hoisting
captures them:

```ocaml
let g_ = outer in
let f = function
  | g_, A, vhs -> use g_        (* the component *)
  | _,  B, vhs -> use g_        (* the OUTER g_ — captured *)
```

Scoping is invisible to an AST comparison and the types usually coincide, so this
stage rests on a token scan rather than on the verifier. Sites needing it are
declined *whole* under the default stage — never half-hoisted — so the later run
still finds a `function` to rewrite.

The scan is `usable`: a Mix position may be hoisted only if every branch that
binds `_` there mentions the name nowhere in its own pattern, guard or body. A
branch binding the name at that very position is exempt, since it re-binds it to
the component the parameter holds. Where the scan fails, the position is *demoted*
back into the scrutinee rather than the site being lost — the `_` branches keep
their `_` and go on reading the outer binding.

Run over the 102 declined sites, `--with-any` rewrote **99** (498 edits, 54 files,
again 0 escalations), demoted **5** positions, and declined 3 sites outright for
having nothing left to hoist. `src/Frontend/ParseMode.ml:185` is the shape the
guard exists for:

```ocaml
let parseModeParen = function
  | LS.Cons ((L.Id (_, name), r0), s'), r -> … P.join r r' …
  | LS.Cons ((t, r), s'), _              -> Parsing.error r …
```

Hoisting `r` would put a parameter where the second branch expects its own
pattern binding. Here the inner `(t, r)` would in fact have shadowed it, so the
decline is conservative rather than necessary — which is the intended direction.

## Guards, stated so they are not relaxed later

A position may be dropped only if it is irrefutable in every branch, and
irrefutable here means `Ppat_var` or `Ppat_any` and nothing else. That is what
makes branch *selection* provably identical. In addition:

- `pvb_constraint = None`. `let f : t = function …` would splice to
  `let f (g_, tm, vhs) : t = match …`, silently reinterpreting `t` as the return
  type.
- No attributes on the `Pexp_function` or the `Pfunction_cases`.
- Every `pc_lhs` is a `Ppat_tuple (_, Closed)` with all components unlabelled;
  5.5 labelled tuples would break reconstruction. A top-level `Ppat_alias`
  (`| (g_, A, vhs) as p ->`) or `Ppat_or` falls out of this requirement rather
  than being special-cased.
- No comment may sit anywhere in a case pattern *outside* a component that is
  kept. Text inside a kept component is copied through verbatim, so
  `| g_, Omitapx (…, r (* = Vhs *)), vhs ->` is fine; a comment in a dropped
  component would be deleted, which is how the `letunit` pass lost one.

## Naming

Hoisted positions keep the name every branch already gave them. A position that
*stays* in the scrutinee still needs a parameter name:

- **Reuse a branch's binder** where one exists and no *other* branch mentions it
  — 215 positions, including the worked example, which comes out as
  `checkExact1 (g_, tm, vhs) = match tm with` exactly as specified.
- **Otherwise a fresh `a`, `b`, …** — 1,010 positions.

Candidates are judged against the *cases* region, not `file_words`. The parameter
is bound over the `match` and nothing else, so that is the only region it can
capture in; scanning the whole file instead pushed almost every name out to `a2`
or `a4`, because nearly every file in the tree contains some `a` somewhere. A
case that itself binds `n` at that position is exempt — it re-binds `n` to the
component the parameter already holds, so the shadowing is inert.

Name derivation degrades, it never blocks: a failed scan yields
`(g_, a, vhs) = match a with`, never a decline and never an escalation.

## Layout

The `match … with` stays on the `=` line and only the `function` keyword and the
case *pattern* spans are replaced, so every `|` column and every body line is
untouched. No re-indentation machinery is involved, and `= \n function` keeps its
line break. `DEFUN1` is the one exception: it collapses `= function | p ->` to
`(p) =` in a single edit, because two edits would leave the keyword's line blank.
