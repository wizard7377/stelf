# Test Directory Changes: HEAD@{4} → HEAD

Two commits: `eec20f0` (added many more pal tests) and `3c972a4` (fixed pal tests).  
Three files changed: `test/Pal/Common.ml`, `test/Pal/Cases.ml`, `test/Pal/Source.ml`.  
Net diff: **+1408 / −78 lines**.

---

## `test/Pal/Common.ml` — Test infrastructure refactor

### `test` return type

The `test` helper changed from producing a single Alcotest case per test suite to producing one case *per command*:

```
(* before *)
val test : ?skip:bool -> ?failure:bool -> string -> string list -> unit Alcotest.test_case

(* after *)
val test : ?skip:bool -> ?failure:bool -> string -> string list -> string * unit Alcotest.test_case list
```

Each command in the input list becomes its own Alcotest case, named `"<suite> - 1"`, `"<suite> - 2"`, etc. This makes it possible to see *which* command in a multi-step test failed, rather than only knowing the suite name.

### `tester` class

A new stateful `tester` class wraps a `Pal.pal` instance:

```ocaml
class tester = object
  val mutable p = new Pal.Pal.pal
  method run cmd = ...   (* returns exn option *)
  method reset () = p <- new Pal.Pal.pal
end
```

A single `tester` is created per `test` call and shared across all commands in that call. This is critical: STELF declarations are stateful — `%sort nat` in command 1 must still be in scope for `%term z nat` in command 2.

### `has_failed` ref

A `has_failed` ref is initialized to `false` and set to `true` when any command raises. Subsequent commands in the same suite check this flag and call `Alcotest.skip ()` if it is set. This gives fail-fast semantics within a suite while still individually registering (and skipping) remaining cases.

### Backtrace capture

On failure the exception backtrace is now captured (`Printexc.get_backtrace ()`) and included in both the `eprintf` output and the `Alcotest.failf` message, making it much easier to locate the source of a runtime error in the Pal frontend.

---

## `test/Pal/Cases.ml` — Wiring refactor and new suites

### Adaptation to new `test` return type

All existing suite definitions were updated. The old pattern:

```ocaml
[ test "name" src_list ]
```

became:

```ocaml
List.concat [ snd (test "name" src_list) ]
```

`snd` strips the name string (the first component of the new return type), and `List.concat` flattens the list of per-command cases.

### New `cases ()` definition (shadows the old one)

A second `let cases () = ...` definition is added at the bottom of the file, shadowing the first. It uses a flat `Alcotest.run "PAL"` call with a single `test` invocation per conceptual example, passing all source chunks for that example as a single list. This is the entry point actually executed by the test binary.

The new `cases ()` runs 25 named suites:

`%term and %sort`, `FOL`, `ZF`, `Nats`, `S4`, `LAM`, `POLYLAM`,
`PROP-CALC`, `MINI-ML`, `ARITH`, `GUIDE-LISTS`, `TAPL-NAT`,
`LP-HORN-ND`, `CHURCH-ROSSER-LAM`, `CUT-ELIM-FORMULAS`, `GUIDE-ND`,
`CPSOCC-DSBNF`, `SMALL-STEP-LAM`, `CRARY-EXCON`, `CRARY-EXCON-REV`,
`TAPL-DEFS`, `SMALL-STEP-SYSF`, `SMALL-STEP-SYSF-ISO`,
`POPLMARK-1A`, `POPLMARK-2A` (known runtime failure — see below), `CCC`, `INCLL`,
`CRARY-LINEAR`, `CRARY-LINEARD`, `CRARY-MODAL`.

---

## `test/Pal/Source.ml` — STELF source changes

### A. Modifications to existing source strings

These are bug fixes to STELF code that was already in the file.

---

#### `fol2` — spurious implicit on `f1` removed

```diff
-%term f1 {{A}} {T i} hil ((forall [x i] A x) imp (A T))
+%term f1 {T i} hil ((forall [x i] A x) imp (A T))
```

`A` is the predicate being universally quantified. In the original, `{{A}}` asked the elaborator to infer `A` as an implicit argument of `f1` itself — but `A` does not appear free in `f1`'s conclusion type `hil (...)` in a way that lets the elaborator solve for it at a call site. The fix promotes `A` to be inferred from the body of the `forall` binder instead, which reconstruction can handle.

---

#### `fol4_1` — `hnd_n1` implicit arguments removed

```diff
-%term hnd_n1 {{A B}} hilnd n1 (impi [u] impi [v] noti [p] [w] note (impe u w) p (impe v w))
+%term hnd_n1 hilnd n1 (impi [u] impi [v] noti [p] [w] note (impe u w) p (impe v w))
```

`A` and `B` are the formula types, but they do not appear in the proof term body — only in the type of `n1` (a Hilbert axiom). The `{{A B}}` declaration asked STELF to solve for them at call sites, but they are unconstrained by the arguments given. Removing the implicits lets reconstruction determine them solely from the type of `n1`.

---

#### `fol4_1` — `hnd_f1` rewritten with binder type annotation

```diff
-%term hnd_f1 {{A}} {T i} hilnd (f1 T) (impi [u] foralle u T)
+%term hnd_f1 {{A T}} hilnd (f1 T) (impi [u nd (forall [x i] A x)] foralle u T)
```

Two changes:
1. `T` is promoted from an explicit argument `{T i}` to an implicit `{{A T}}`. Since `T` appears in the conclusion `hilnd (f1 T) (...)`, reconstruction can infer it.
2. The lambda binder `[u]` in `impi` is annotated with its full type `nd (forall [x i] A x)`. Without this annotation, STELF's reconstruction could not determine the type of `u`, because `foralle u T` does not constrain what sort `u` inhabits.

---

#### `fol4_2` — `%mode` changed to named-argument form

```diff
-%mode hilnd %in %out
+%mode {%in X _} {%out Y _} hilnd X Y
```

STELF's `%mode` declaration requires explicit argument names when describing a relation with multiple arguments. The shorthand `%in`/`%out` positional form was not accepted; the named form `{%in X _} {%out Y _}` is required. The same fix applies to `ndhil` in `fol6_2`.

---

#### `fol5` split into `fol5_1` + `fol5_2`

The original `fol5` string is split into two parts concatenated as `fol5 = fol5_1 ^ fol5_2`. The split separates term declarations from meta-declarations (`%block`, `%mode`, `%worlds`, `%total`), allowing each chunk to be loaded independently if needed and making it easier to test them incrementally.

Several fixes within `fol5`:

**`ded_id` binder annotation:**
```diff
-%term ded_id {{A}} ded ([u] u) (mp (mp s k) k)
+%term ded_id {{A}} ded ([u hil A] u) (mp (mp s k) (%the (hil (A imp (A imp A))) k))
```
The identity deduction `[u] u` needed an explicit type `hil A` on `u` so reconstruction knows which sort the identity proof inhabits. The `%the` annotation on `k` pins the type of the axiom application.

**`ded_ug` implicits consolidated:**
```diff
-%term ded_ug {{A B}} {H1 {_ hil A} {_ i} hil _} {H1' {_ i} hil _} {_ {a i} ded ([u] H1 u a) (H1' a)} ded ([u] ug (H1 u)) (mp f2 (ug H1'))
+%term ded_ug {{A B H1 H1'}} {_ {a i} ded ([u] H1 u a) (H1' a)} ded ([u] ug (H1 u)) (mp f2 (ug H1'))
```
`H1` and `H1'` were explicit higher-order arguments. They are now in the `{{...}}` implicit group, which STELF can infer from the `ded` premise.

**`lded` block binder annotation (moved to `fol5_2`):**
```diff
-%block lded [A o] {u nd A} {v hil A} {h {C o} ded ([w] v) (mp k v)}
+%block lded [A o] {u nd A} {v hil A} {h {C o} ded ([w hil C] v) (mp k v)}
```
The lambda `[w]` in the `ded` premise of the block needs an explicit type `hil C` to allow reconstruction to check the block declaration.

---

#### `fol6` split into `fol6_1` + `fol6_2`, `ndh_*` terms rewritten

All six `ndh_*` term declarations are simplified by consolidating explicit higher-order arguments into the `{{...}}` implicit group.

**`ndh_impi`:**
```diff
-%term ndh_impi {{A1 B}} {D1 {_ nd A1} nd B} {H1 {_ hil A1} hil B} {H1' hil (A1 imp B)} {H1'' ...} {_ ded H1 H1'} {_ {u nd A1} {v hil A1} {_ ...} {_ ndhil u v} ndhil (D1 u) (H1 v)} ndhil (impi D1) H1'
+%term ndh_impi {{A1 B C D1 H1 H1' H1''}} {_ ded H1 H1'} {_ {u nd A1} {v hil A1} {_ {C o} ded ([w hil C] v) (mp k v)} {_ ndhil u v} ndhil (D1 u) (H1 v)} ndhil (impi D1) H1'
```
`D1`, `H1`, `H1'`, `H1''` (higher-order metas) moved to `{{...}}`; binder `[w]` annotated as `[w hil C]`.

**`ndh_impe`, `ndh_note`, `ndh_foralli`, `ndh_foralle`:** same pattern — all per-argument explicit metas folded into `{{...}}`.

**`ndh_noti`:**
```diff
-%term ndh_noti {{A1}} {D1 ...} {H1 ...} {H1' ...} {H1'' ...} {_ ded (H1 A1) H1''} {_ ded (H1 (not A1)) H1'} {_ {p o} {u nd A1} ... ndhil (D1 p u) (H1 p v)} ndhil (noti D1) (mp (mp n1 H1') H1'')
+%term ndh_noti {{A1 H1 H1' H1'' D1}} {_ ded (H1 (not A1)) H1'} {_ ded (H1 A1) H1''} {_ {p o} {u nd A1} {v hil A1} {_ {C o} ded ([w hil C] v) (mp k v)} {_ ndhil u v} ndhil (D1 p u) (H1 p v)} ndhil (noti D1) (mp (mp n1 H1') H1'')
```
Note the argument order of the two `ded` premises is swapped (negation premise first, affirmation second) in addition to the implicit consolidation.

**`%mode` and `lndhil` block (in `fol6_2`):**
```diff
-%mode ndhil %in %out
-%block lndhil [A o] {u nd A} {v hil A} {h {C o} ded ([w] v) (mp k v)} {nh ndhil u v}
+%mode {%in X _} {%out Y _} ndhil X Y
+%block lndhil [A o] {u nd A} {v hil A} {h {C o} ded ([w hil C] v) (mp k v)} {nh ndhil u v}
```
Same `%mode` named-argument fix as `hilnd`; same `[w hil C]` binder annotation as `lded`.

---

### B. New STELF source strings added

All new strings are ported from `twelf/examples/`. Each is a `let` binding in `Source.ml` whose value is an OCaml raw string literal containing STELF declarations.

| Binding(s) | Upstream file | LF features exercised |
|---|---|---|
| `nats1`–`nats4` | (original) | `%sort`, `%term`, `%mode`, `%worlds`, `%total` |
| `prop_calc_types`, `prop_calc_hilbert`, `prop_calc_nd` | `prop-calc/prop-calc.elf` | `%prec %right`, Hilbert axioms, natural deduction |
| `mini_ml_exp`, `mini_ml_value`, `mini_ml_tp` | `mini-ml/mini-ml.elf` | Recursive types, `%mode` on value predicate |
| `arith_nat`, `arith_nt`, `arith_plus`, `arith_acker` | `arith/arith.elf` | Ackermann function; `%mode`, no `%terminates` |
| `guide_lists_types`, `guide_lists_append`, `guide_lists_mode` | `guide/lists.elf` | List append with full `%mode`/`%worlds`/`%total` |
| `tapl_nat_base`, `tapl_nat_eq` | `tapl_ch13/nat.elf` | `nat_eq`, `nat_neq`, `nat_lt` |
| `lp_horn_nd` | `lp_horn/natded.elf` | First-order logic ND with `forall`/`pf` |
| `church_rosser_lam` | `church_rosser/lam.elf` | Untyped lambda term syntax only |
| `cut_elim_formulas` | `cut_elim/formulas.elf` | Predicate calculus with `or`/`not`/`false` |
| `guide_nd` | `guide/nd.elf` | Full intuitionistic ND; `%block`, `%worlds`, `%sort red` |
| `cpsocc_dsbnf` | `cpsocc/dsBNF.elf` | CPS/BNF term sorts (`droot`/`dexp`/`dtriv`) |
| `small_step_lam_types` … `small_step_lam_step` (5) | `small_step/lam.elf` | STLC: `%sort tp tm`, `%prec %left`, infix `=>` `@` `~>` |
| `crary_excon` | `crary/explicit/excon.elf` | Explicit context LF: `of`, `pi` dependent type, `leq` |
| `crary_excon_rev_syntax` | `crary/explicit/excon-rev.elf` | Reversed context variant; adds `ctx`/`nil`/`cons` |
| `tapl_defs_types` … `tapl_defs_heap` (6) | `tapl_ch13/defs.elf` | STLC + references: store/heap with `%mode`/`%worlds`/`%total` |
| `small_step_sysf_types` … `small_step_sysf_step` (5) | `small_step/system_f.elf` | System F: `forall`, `Lam`/`#` type abstraction/application |
| `small_step_sysf_iso_types` … `small_step_sysf_iso_step` (5) | `small_step/system_f_iso.elf` | System F + iso-recursive `mu`/`roll`/`unroll` |
| `poplmark_1a_syntax` | `poplmark/1a.elf` | F-sub subtyping: `top`, `forall`, `assm`/`sub` |
| `poplmark_1b_syntax` | `poplmark/1b.elf` | F-sub + record rows: `trow`, `label`, `trow_order`, `sub_tp_trow` |
| `poplmark_2a_syntax` | `poplmark/2a.elf` | System Fw + typing (known runtime failure — `of`/`term`/`value` conflict with earlier suite state) |
| `poplmark_2b_syntax` | `poplmark/2b.elf` | System Fw + records: `bterm`/`erow`/`pattern`/`prow` |
| `ccc_syntax` | `ccc/ccc.elf` | Cartesian closed category: `obj`/`mor`/`meq`, `prod`/`exp_obj` |
| `incll_syntax` | `incll/incll.elf` | Intuitionistic linear logic: `eval`, `frm`/`atm`, `forall2` |
| `crary_linear_syntax`, `crary_linear_linear` | `crary/substruct/linear.elf` | Linear substructural types: `lolli`/`tensor`/`with`/`bang`, `linear` predicate |
| `crary_lineard_syntax` | `crary/substruct/lineard.elf` | Dual linear: adds `pi` dependent type, `ulam`/`uapp` |
| `crary_modal_syntax` | `crary/substruct/modal.elf` | Modal types: `box`/`diamond`, `bx`/`letbx`/`di` |

#### Porting notes common to new strings
- `%infix` directives from Twelf → `%prec %left`/`%right` in STELF.
- `%name` hints, `%freeze`, `%query`, `%compile` dropped (not supported).
- Numeric identifiers (e.g. Twelf `1 : nat`) renamed (`zero`).
- Single-character operator names that could conflict with the STELF lexer (e.g. `|`, `^`) replaced with alphabetic names.
- `%theorem`/`%prove` blocks dropped (Twelf automation not in STELF).
- Higher-order proof families that require unsupported `%block some {...}` forms dropped; only syntax declarations retained in such cases.
