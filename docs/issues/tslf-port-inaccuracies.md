# Port inaccuracies in `new-tests2/tslf/sing/`

**Labels:** corpus, port

## Summary

`new-tests2/tslf/sing/` is a mechanical port of Karl Crary's "singleton
kinds" Twelf development, sourced from the `twelf/` submodule at
`twelf/TEST/crary/tslf/sing/*.{elf,thm}` (introduced in commit
`af28e118a`). This note catalogs concrete inaccuracies the port introduced,
each verified against the pristine upstream source so it can be
distinguished from content the mechanical translation handled faithfully.

**Method.** An item only counts as a port inaccuracy here if it (a) differs
from the corresponding upstream `.elf`/`.thm` text and (b) is not an
intentional, documented STELF-side translation. Two plausible-looking
candidates were checked and explicitly **rejected** by this filter — see
[Audited, no defect found](#audited-no-defect-found-comment-conversion) and
[Out of scope](#out-of-scope-an-engine-tolerance-gap-not-a-port-defect)
below. In general, defects concentrate where the porter had to invent a
transformation Twelf has no direct equivalent for (STELF-only `%scope`
sessions, the anonymous-declaration convention, the arrow→binder
desugaring) — not in content that mapped one-to-one, which the mechanical
port handled correctly throughout.

## Finding 1: primitive-reference shadowing via `%scope`

STELF invented `%scope NAME %term LABEL` (`src/Fronts/Pal/Impl.ml`) so that
sibling case-clauses of a judgment could refer to each other unqualified —
implemented by modeling each `%scope` session as a real Twelf
structure/module and installing bare-name visibility via
`Names.insertConstShadow`/`installConstName`, mutating a global
`topNamespace`. Upstream Twelf has no equivalent mechanism (it never
shadows a primitive constant this way), so this is a bug class the port
introduced by construction: a case-label that happens to share a name with
a real object-level primitive (`pi1`, `at`, `sing`, ...) silently shadows
that primitive for the rest of its open `%scope` session, breaking any
sibling clause's legitimate bare reference to it.

**Example**, `new-tests2/tslf/sing/strengthen-thm.lf` (`wf-noassm`/`pi2`
clause, before this session's fix):

```
%scope wf-noassm %term pi1
	%pi (aof-noassm ([x] aof/pi1 (D1 x)) Deqa' DeqA)
	%<- (aof-noassm D1 Deqa DeqAB)
	%<- ({x} atom-resp-atom pi1 (Deqa x) (Deqa' x))
	...
```

The `%scope wf-noassm %term pi1` label installs a case named `pi1`, which
then shadows `il.lf`'s real `pi1 : atom -> atom` primitive for the rest of
the session — so this clause's own reference to the true primitive
(`atom-resp-atom pi1 ...`) resolves to the wrong thing, producing a
`[recon] Type mismatch` at load time. The fix (implemented this session)
was a new `%abs NAME` qualifier that resolves to the toplevel declaration
within the currently-loading `%require` group, bypassing `%scope`
shadowing: `atom-resp-atom (%abs pi1) (Deqa x) (Deqa' x)`.

**Scope of the defect:** a purpose-built scanner found and fixed roughly
700 instances of this pattern across `strengthen-thm.lf`,
`explicit-lemmas-thm.lf`, `substitution-thm.lf`, `expand-thm.lf`, and
`complete-thm.lf`. A related variant also appears where a case-label should
have reopened an existing `%scope` session but was left bare because an
unrelated judgment's `%sort`/`%mode`/`%worlds`/`%total` block separated it
from its siblings (fixed manually in `substitution-thm.lf`'s
`app`/`pi1`/`pi2`/`at-o`/`at-ao`/`at-a` clauses).

**Severity:** fatal at load time (`[recon] Type mismatch`, or `Shadowing`
for the missed-reopen variant) — the best-attested and highest-value entry
in this catalog.

## Finding 2: anonymous declarations becoming a real, reusable name

Upstream Twelf's anonymous top-level declaration `-	: TYPE -> type.` has no
name at all: Twelf assigns it a fresh, internally-unnameable identity, and
the idiom is written repeatedly across the corpus without ever colliding.
The port rewrote every instance as `%sort _ ...` — using the literal
identifier `_` as the declared name.

**Example:**

upstream, `twelf/TEST/crary/tslf/sing/ile.elf:6`:
```
-	: (isvar _ _ -> isvar _ _) -> type.
```

STELF, `new-tests2/tslf/sing/ile.lf:3`:
```
%sort _ {_ %pi (isvar _ _) %-> (isvar _ _)} %.
```

**Scope of the defect:** 14 occurrences survive across 5 files:
`inversion-thm.lf` (×8), `convert-sub-thm.lf` (×3), `translate.lf` (×1),
`convert-effect-thm.lf` (×1), `ile.lf` (×1).

**Severity:** latent/masked. The corpus load has passed through files with
multiple `_`-named sorts (e.g. `inversion-thm.lf`'s eight) without a
`Shadowing` error being reported for `_` specifically, so something
downstream currently tolerates the reused literal name — but this is not a
guarantee to rely on, and the representation itself is wrong regardless of
whether it currently manifests as a crash: it silently depends on STELF's
naming layer never treating `_` as an ordinary collidable constant name at
declaration position, which is not documented behavior.

## Finding 3: `A -> B` desugared to an anonymous dependent binder `{_ A} B`

Already documented in
[`anonymous-binder-reconstruction.md`](anonymous-binder-reconstruction.md):
an anonymous binder `{_ A} B` is semantically a non-dependent function type
(the bound variable is unnameable, so `B` can never reference it), but
STELF's reconstruction originally routed it through the *dependent* `Pi_`
path, elaborating `B` in a context extended with the `_ : A` binder — so
any `Omitted` (`_`) placeholder in `B` gets raised over `A` during
abstraction, turning a first-order implicit into a spurious higher-order
one. Upstream Twelf source never produces this shape at all: it always
writes plain arrows as `A -> B`, which is routed through the correct,
non-dependent `Arrow_` path.

The STELF port re-expressed Twelf's `A -> B -> ... -> type.` argument
chains using STELF's own `{_ A} {_ B} ...` juxtaposition-sort syntax
instead of the semantically-matching arrow form — introducing a
representation Twelf's own source could never have exercised, and one that
was later found to be unsound in general.

**Example**, `twelf/TEST/crary/tslf/sing/expand.thm:1321-1326` vs
`new-tests2/tslf/sing/expand-thm.lf:392`:

```
sub-expand-var-e	: wfe G A
			   -> ({x} isvar x I -> ofe (cons G x A) (M x) (B x))
			   -> ({x} expand x A (X x))
			   -> ({x} sub ([x] M x) (X x) (M x)) -> type.
```
```
%sort sub-expand-var-e {_ wfe G A} {_ {x} %pi (isvar x I) %-> (ofe (cons G x A) (M x) (B x))} {_ {x} expand x A (X x)} {_ {x} sub ([x] M x) (X x) (M x)} %.
```

(Argument count and order are faithful here — spot-checked across several
declarations — the defect is purely the choice of representation, not
corruption of arity.)

`factor_sort` (`src/Fronts/Pal/Impl.ml`) now special-cases anonymous
(`None`-named) sort argument decls to emit the non-dependent `Arrow_` form
instead of `Pi_`, which covers every surviving `{_ ...}` occurrence in this
corpus — a corpus-wide sweep confirms none remain outside `%sort`
argument-kind position. But per the issue doc's own "still open" section,
an anonymous `{_ A} B` written directly in an arbitrary term or type
position (not a sort kind, not `%->`/`%<-` sugar) still goes through the
dependent path and would still over-scope; this corpus simply never
exercises that case.

**Severity:** fixed for every occurrence this corpus contains;
architecturally still open in general.

## Audited, no defect found: comment conversion

Explicitly checked and found faithful:

- **`%{ ... %}` → `%[ ... %]`** (seen in `explicit-lemmas-thm.lf`, wrapping
  a block of superseded lemmas Crary had already block-commented out
  upstream). This looked like a malformed comment delimiter at first
  glance, but it is the **documented, intentional** STELF replacement for
  Twelf's block comment: "in the outer context a bare string is ignorable
  prose (this replaces the old `%{ ... %}` block comment)"
  (`docs/grammar.md:93-98`). Not a mistranslation.
- **Section-divider cosmetic variants** (`%%%%  Header  %%%%%` vs
  `%%%%%  Header  %%%%%`, an extra leading space before a divider, bare
  `%%%` with no header text) are functionally inert regardless of exact
  percent-count, and the bare `%%%` variant is present verbatim upstream
  too (e.g. `complete.thm` lines 623, 666, 787, 880) — not introduced by
  the port.
- **Nested block comments**: none exist anywhere in the upstream `sing/`
  source, so there was no nested-comment case for the port to mishandle.

## Out of scope: an engine-tolerance gap, not a port defect

`expand-thm.lf` declares `tsub-expand-var-e` twice (lines 384 and 494)
with matching signatures but different proof bodies, and
`convert-reg-thm.lf`/`convert-fun-thm.lf` both declare `vconvert-fun` with
identical signatures but different `%worlds` contexts. Both pairs are
present **verbatim** in the upstream source
(`expand.thm:1305`/`expand.thm:1546`;
`convert-fun.thm:154`/`convert-reg.thm:938`, both loaded into the same
flat namespace per `sing/sources.cfg`) — the port did not introduce this
duplication.

This means upstream Twelf tolerates a same-name redeclaration that STELF's
namespace layer currently rejects with a fatal `Shadowing` error. That is
an **engine/loader behavioral gap** between STELF and upstream Twelf, not a
corpus-port defect, and is explicitly excluded from the categorized
findings above.

## Category mapping

| Finding | Names not scoped / anonymous→regular | Incorrect conversion | Comment conversion | Incorrect name conversion | Command misuse | Bad name reference | Wrong construct |
|---|---|---|---|---|---|---|---|
| 1. `%scope` shadowing | ✓ | | | | | ✓ | |
| 2. `-` → `_` | ✓ | | | ✓ | | | |
| 3. `A -> B` → `{_ A} B` | | ✓ | | | | | ✓ |
| Comments (audited clean) | | | *no defect* | | | | |
