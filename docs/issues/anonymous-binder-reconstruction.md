# Anonymous binders `{_ A} B` are reconstructed as dependent `Pi`, over-scoping omitted variables

**Labels:** bug, reconstruction

## Summary

An anonymous binder `{_ A} B` (a `{ }` binder whose bound variable is `_`) is
semantically a **non-dependent** function type `A -> B`: the bound variable has
no name, so `B` can never reference it. But STELF's term reconstruction routes
`{_ A} B` through the *dependent* `Pi_` path
([`src/Recon/ReconTerm.ml`](../../src/Recon/ReconTerm.ml), `Pi_` case), which
elaborates the codomain `B` in a context **extended with the `_ : A` binder**.
Any `Omitted` (`_`) placeholder appearing in `B` is therefore created under that
binder and, during abstraction ([`src/IntSyn/Abstract.ml`](../../src/IntSyn/Abstract.ml),
`raiseType`), gets **raised over `A`** — turning what should be a first-order
implicit `{_?n T}` into a higher-order implicit `{_?n {_0 A} T}`.

The non-dependent `Arrow_` path ([`ReconTerm.ml`](../../src/Recon/ReconTerm.ml),
`Arrow_` case) already does the right thing: it reconstructs the codomain in the
*same* context (`eClo (V2, shift)`), so no spurious raising occurs.

This matches how upstream Twelf behaves: Twelf source writes these as
`A -> B` (the `arrow` recon path), never as an anonymous `{_:A} B`, so it never
produces the higher-order implicit.

## Impact

The spurious higher-order implicit passes reconstruction, world-checking, and
termination unnoticed, but breaks the two phases that must *enumerate* against
the argument:

- **Coverage** (`src/Cover/`): matching a clause head whose implicit is
  `_?n Dec_` (raised over a premise) against a world-block parameter becomes a
  non-pattern flex-application unification, left as a constraint, so a covered
  case is reported as a spurious `Coverage error --- missing cases`.
- **Mode checking** (`src/Modes/Modedec.ml`): a higher-order implicit in a
  family kind shifts the argument-position walk in `inferVar`, hitting an
  uncovered pattern → `Match_failure`. (Note: `Modedec.inferVar` is partial in
  exactly the same way as upstream `twelf/src/modes/modedec.fun`; the upstream
  code simply never reaches the partial case because its reconstruction never
  produces this shape. Do **not** "fix" it by patching `Modedec` — fix the
  over-scoping.)

## To reproduce

Before the partial fixes below, `check new-tests2/tslf/stelf.toml` aborted with a
spurious `Coverage error` on `cxt-precedes-trans` in `explicit-context-lemmas.lf`
(clause premise via `%<-`), and — once that was worked around — a `Match_failure`
in `Modedec` on `cxt-bounded-lookup` (family kind via `{_ …}`).

## Fixed / worked around so far

- **`%->` / `%<-` sugar** now desugars to the CST `Arrow` node instead of an
  anonymous `Pi` ([`src/Fronts/Modern/Modern.ml`](../../src/Fronts/Modern/Modern.ml),
  the `%->`/`%<-` folds).
- **Sort argument kinds** now emit `Arrow` for anonymous (`[None]`) argument
  decls and `Pi` only for named ones ([`src/Fronts/Pal/Impl.ml`](../../src/Fronts/Pal/Impl.ml),
  `factor_sort`). This also implements the juxtaposition sort syntax
  `%sort add nat nat nat` ≡ `add : nat -> nat -> nat -> type` and
  `%sort eq {T ty} (tm T) (tm T)` ≡ `eq : {T:ty} tm T -> tm T -> type`.

## Still open (the general case)

An anonymous `{_ A} B` written directly in an arbitrary term/type position
(e.g. inside a `%term` type, or a nested binder telescope that is not a sort
kind and not `%->`/`%<-` sugar) still goes through the dependent `Pi_` path and
over-scopes.

## Proposed fix

Handle anonymous binders uniformly at the reconstruction layer: when a `Pi`
binder's bound variable is anonymous (name `None`), reconstruct it via the
non-dependent `Arrow_` path (codomain in the same context, `depend = No`)
rather than the dependent `Pi_` path. This is always sound — an anonymous
binder can never be referenced — and would subsume both point fixes above.
Candidate site: the CST→recon translation in
[`src/Recon/ReconTerm.ml`](../../src/Recon/ReconTerm.ml) (map a `None`-named
`V.Term.Pi` decl to `Arrow_`), or the `Pi_` reconstruction case itself.
