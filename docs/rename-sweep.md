# Dropping the trailing underscore from local binders

SML allows capitalised variables, so the port mapped `G` to `g_`, `U` to `u_`,
`V` to `v_` and so on. Where no bare `g` was ever in play, the underscore is pure
residue — and `STYLE.md` already asks for it to go.

## Result

| | |
|---|---|
| trailing-underscore tokens in `src/**.ml` before | 27,341 (313 distinct) |
| renamed | **24,792** across 264 names, 145 files |
| declined | 627 binders across 36 names |
| escalated | **0** |
| remaining tokens | 2,859 |

Five batches, each gated on `dune build @check`: `src/Typecheck` as a trial, then
`g_` alone (3,888), `v_ d_ u_` (4,552), a ten-name batch (5,444), then the
remainder (10,644). A second `locate` afterwards reports `RENAME=0`, so the pass
is at a fixpoint.

## Why a whole-region token rewrite is sound

The rewrite renames *every* occurrence of `x_` in one binder's scope at once.
That is sound for a reason worth stating plainly: **within a binder's own scope
there is no free occurrence of the name it binds.** Every `x_` in the region
resolves either to this binder or to an inner one that shadows it, so renaming
them together is a bijection on the region — inner shadowing survives intact,
just spelled without the underscore.

The one thing that can go wrong is capture, and that is exactly what the guard
rules out: the bare name must appear nowhere in the region, so nothing there can
already mean something else.

The guard region is always a *superset* of the true scope, never a subset. It
starts at the binder's own pattern — so the binding occurrence is renamed too —
and runs to the end of the construct. A superset only makes the guard stricter,
and the extra text holds binding positions rather than free uses.

Scope per binder form:

| binder | region |
|---|---|
| a `function`/`fun` parameter | from the parameter to the end of the function |
| `let x_ = e in body` | `body`, plus every right-hand side when `rec` |
| a match case | the case, from its pattern to the end of its body |
| `for x_ = … do … done` | the loop |

## The guard is load-bearing and the verifier does not back it

`Core.verify` catches shape errors; capture is a scoping property. Rename the
wrong thing and the intent tree and the reparse agree perfectly, both wrong.
`src/Typecheck/Typecheck_.ml:115` is the worked counter-example the plan put
there for this: it binds `s_` (a spine) and `s` (a substitution) in one pattern,
same type, so even the compiler would stay silent. **It declines**, as do 261
other `s_` binders — `s_` accounts for 262 of the 627 declines, followed by `g_`
(53), `d_` (52), `s1_` (51), `s2_` (45) and `s'_` (45). Different things wearing
near-identical names is precisely why the port added the underscore, and this is
where it stays.

What the verifier *does* buy is the text-scan errors that are easy to make — a
hit inside a string literal, a record label, a qualified path. It found none:
0 escalations across 24,792 edits.

## Rules, written down rather than emergent

- **`x'_` → `x'` is in scope.** The prime is part of the name and the guard
  treats `g'` exactly as it treats `g`. This matters: `g'_`, `d'_` and `v'_`
  together are ~1,500 occurrences.
- **`x__` is not.** Stripping one underscore leaves another, so the name was
  never underscore-residue.
- **Keyword avoidance is never undone.** `new_`, `module_`, `for_`, `try_`,
  `match_`, `assert_`, `sig_`, `open_`, `type_`, `mod_`, `class_`, `of_`, `to_`,
  `external_`, `end_`, `done_`, `true_` — the rule is computed from the keyword
  set, not a hand list.
- **Comments are skipped**, not rewritten. Only 4 of 4,160 `g_` occurrences
  tree-wide sit in one, so there is no consistency to buy and a large
  unreviewable diff to avoid. String, quoted-string and character literals are
  recognised and skipped for the same reason the verifier exists.
- **Nesting suppression keys on *accepted* sites only.** When an outer site
  declines and an inner one of the same name passes, the inner rename still
  happens: it shadows throughout its own region, so no outer occurrence is
  reachable from inside it.
- **Module-level bindings are out of scope by decision** — the ~11 `val x_`
  declarations and ~47 module-level `let x_ =` (the `Formatter_.ml` cluster:
  `break_`, `space_`, `nl_`, `vbox_`; `Fmt.break_` alone has 141 call sites).
  Parameters of a module-level function are local and *are* renamed; only the
  bound name itself is left. Interfaces hold 4 trailing-underscore tokens against
  27,341 in `.ml`, so this costs almost nothing.
- Constructors, module names and type names are excluded by casing or position;
  labelled arguments do not exist in this tree (`~x_` has zero hits).
