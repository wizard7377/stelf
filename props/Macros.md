# Macro System

## Motivation

STELF has grown a family of derived commands — `%data`, `%prop`, `%proof`,
`%open %require` — each of which is a fixed rewrite into commands that already
exist. Every one of them cost a parser branch, a desugaring function, and a
round of tests. `%data` is thirty lines of `Cmd.ml` to say

```
%data NAME DECLS CMD    ⟶    %sort NAME DECLS %. %scope NAME CMD
```

(`Cmd.ml:352-390`). That is a rewrite a user should be able to write, in STELF,
without touching OCaml.

A macro system already exists in the CST, and was considered for exactly this job
and rejected:

> The CST already has `Macro` / `Use` commands. These shorthands cannot be
> expressed with them: a positional macro substitutes its arguments, whereas
> `%prop` and `%proof` must *compute* new syntax from theirs — erasing modes to
> get `DECLS`, projecting names to get `ARGS`, blanking non-input positions to
> get `CALL_PAT`. That is a structural transformation, not a substitution, so it
> has to live in the parser (or in a dedicated desugaring pass over the CST).
>
> Also the macro system is not ready for use yet.
>
> — `cmsg.md:346-355`

**This proposal is an overhaul of that system, addressing both halves of that
verdict.** Substitution becomes computation, via two additions:

- a **class system**, so a macro parameter can be a kind, a mode, or a whole
  command — not only a term, which is all the current engine substitutes
  (`MACRO.ml:8`);
- **imperative forms**, a small set of `%#…` operations that compute over names
  and commands rather than merely copying them.

The goal is not a general-purpose language. It is to make the *next* `%data`
a library definition instead of a compiler change.

## Current state

What exists today, and what this proposal changes.

| Piece | Where | Status |
|---|---|---|
| `Macro_ of int * string * cmd` | `Cst.ml:227` | Arity, name, body. **No class list** — replaced below |
| `MacroParam_ of loc * int option * int` | `Cst.ml:67` | `(level, index)`; index is 1-based. Retained |
| `Use_ of string list * term list` | `Cst.ml:235` | Parses; meaning contested — see §9 |
| Substitution engine | `Macro.ml` | Works over the whole `Cmd` view. Extended, not replaced |
| `apply : t -> C.term list -> C.cmd` | `MACRO.ml:8` | **Terms only** — generalised below |
| `%use NS.NAME (args)` | `Cmd.ml:517-526` | Parses; rejected downstream (`Impl.ml:883`) |
| `%macro` surface syntax | — | **Does not exist.** Macros are unwritable today |
| Frontend support | `Impl.ml:886` | `failwith' "Macros not yet implemented"` |
| `MacroParam` surface syntax | `stelf.md:498` | Listed among terms the parser never produces |

So the engine is roughly half-built and entirely unreachable: there is no way to
write a macro, and the one frontend that could run one refuses. Nothing here is
load-bearing for existing code, which means the overhaul is unconstrained by
backwards compatibility.

## Definitions

Terminology used throughout, so the rules can be stated precisely.

| Term | Meaning |
|---|---|
| **command** | Anything acceptable to `%scope NAME` — a single command or a brace-delimited sequence `%{ … %}` (`Cmd.ml:213-215`). In the CST a sequence is `Cmd.Eval (loc, cmds)` |
| **class** | The syntactic category of a macro parameter; see §5.2 |
| **parameter** | A hole in a macro body, written `%arg NAME N` or `%N` |
| **level** | Which enclosing macro a parameter belongs to. `MacroParam_`'s `int option` field: `None` = the innermost macro, `Some j` = the macro at nesting depth `j` |
| **argument** | The syntax supplied at a use site, bound to a parameter |
| **expansion** | The phase between parsing and elaboration that eliminates all macros |
| **imperative form** | A `%#…` operation evaluated during expansion (§8) |
| **macro table** | The parser-threaded map from macro name to its class list (§6) |

## Basics

Macro expansion is a phase between parsing and elaboration. It consumes a CST
containing macro definitions, applications, and imperative forms, and produces a
CST containing none of them.

Macros are deliberately **not** a general-purpose language. They are abbreviations
for common sequences of commands, plus enough computation to derive one form of
syntax from another.

## Syntax

### 5.1 Definition and application

```
%macro "(" CLASS* ")" NAME CMD
```

A macro named `NAME`, whose parameters have the given classes in order, expanding
to `CMD`. The body must be **exactly one command** — which, since `%{ … %}` is a
command, is not a real restriction.

Application is bare juxtaposition: `%NAME arg1 arg2 …`. Every non-reserved
syntactic term preceded by `%` starts a new toplevel command, and is therefore a
macro application. This is the syntactic core of the proposal: `%` stops being a
closed keyword set.

Arity is fixed by the class list, so application needs no delimiters. The parser
consequently has to know each macro's arity before it can parse a use site — see §6.

### 5.2 Classes

A class constrains what a parameter may be bound to, and tells the parser how to
read the corresponding argument. Syntactically any identifier is accepted in the
class list; only the following are meaningful.

| Class | Admits | Notes |
|---|---|---|
| `term` | Any term | |
| `sort` | Any term | Alias of `term`; use it for documentation value |
| `kind` | A sequence of `{…}` declarations | What follows the name in `%sort` (`Cmd.ml:339-349`) |
| `mode` | Any `%mode` declaration | Short or full form |
| `full-mode` | A `%mode` declaration built **only** from `{%MODE …}` entries | The form `%prop`/`%proof` consume (`cmsg.md:53-66`) |
| `meta` | A `kind` whose entries are in `full-mode` form | A kind carrying modes; see §5.4 |
| `lid` | An unqualified identifier | |
| `id` | An unqualified identifier | Alias of `lid` |
| `rid` | Any identifier, qualified or not | |
| `value` | An `rid` or a string literal | Prolog-atom-like; consumed by `%#ECHO` |
| `modality` | One of `%in`, `%out`, `%star`, … | The `mode` type is `Plus_ \| Star_ \| Minus_ \| Minus1_` (`Cst.ml:145`) |
| `macro` | A command head — `%term`, `%sort`, another macro | Lets a macro abstract over which command it emits |
| `cmd` | A full command, including `%{ … %}` | |
| `param` | A macro parameter | Anything except a class |

### 5.3 Referring to parameters

```
%arg NAME N
```

is the form to write. `NAME` names the macro whose parameter list is meant, and
`N` indexes it **from the first parameter, 1-based**. Naming the macro rather
than counting nesting depth is what makes nested macros readable, and it is
stable: adding a parameter to an enclosing macro renumbers nothing.

```
%N
```

is shorthand for parameter `N` of the innermost enclosing macro. It is what the
printer emits, and corresponds to `MacroParam_ (loc, None, n)`; the named form
corresponds to `MacroParam_ (loc, Some level, n)`, which is why the engine already
carries an `int option` there (`Macro.ml:55-61`).

> [!NOTE]
> The current engine resolves `Some j` only when the traversal depth `i` exceeds
> `j` (`Macro.ml:58`), leaving deeper references untouched for an outer pass to
> handle. The overhaul keeps this; it is what makes nested definitions work.

### 5.4 Modes in kinds

The grammar for kinds is widened to admit mode annotations, so that a `meta` or
`full-mode` argument can be spliced into a kind position without a separate
syntactic category.

Widening the *grammar* is not widening the *language*: `%sort` still rejects a
kind carrying modes. Writing

```
%sort nat {%in _ nat} {%out _ nat}
```

is an error, and the mode-free `%sort nat {_ nat} {_ nat}` is what was meant. To
accept modes deliberately — inside a macro that is deriving a `%mode` from the
same kind — use `%#SORT` (§8.2), which is `%sort` without the check.

### 5.5 Re-reserving `%#`

`%…` was reserved. Because macros *un*-reserve it, `%#…` is re-reserved in its
place, for the imperative forms of §8. No user macro may be named `#…`.

## Parsing

Definitions and parameters parse straightforwardly. Applications do not.

An application `%NAME a b c` is only parseable if `NAME`'s arity is known, and
in general it is not known at parse time. The parser therefore threads a
**macro table** mapping each name to its class list. On reaching an application,
the parser looks the name up, parses that many arguments according to their
classes, and continues.

Because a macro body may itself contain `%macro` definitions (§7.3), a table
entry must also record the macros that definition would introduce, transitively.
Registering an outer macro registers its inner ones.

Two consequences worth stating plainly:

- **An unknown `%foo` is a parse error**, not a deferred lookup. There is no way
  to parse arguments for a macro of unknown arity.
- **Definition must precede use in file order** for the parser to succeed, even
  though *resolution* is dynamic (§7.2). This is a parsing constraint, not a
  scoping one.

## Defining macros

### 7.1 Two phases

Macros are defined in two phases:

1. **File-local**, during macro expansion. A macro defined in a file may be used
   later in the same file.
2. **Global**, during elaboration. A macro defined in one file may be used in
   another that requires it.

### 7.2 Recording versus resolution

The draft of this document contained an apparent contradiction here; it is worth
separating the two axes explicitly.

- **Definitions are recorded at the current scope.** A `%macro` inside
  `%scope foo` belongs to `foo`.
- **Resolution is dynamic.** A macro's body is interpreted at the scope where it
  is *used*, not where it was defined. A body naming `bar` resolves `bar` against
  the use site.

Macros are therefore **not hygienic and not lexically scoped**, by choice. The
purpose is to emit declarations that interact with the surrounding scope — a
macro that could not capture the names around it could not write `%scope` blocks
usefully. Users get the same discipline as C's preprocessor, and the same hazards.

### 7.3 Nested definitions

A macro may define another macro. Parameters of the inner and outer macros are
distinguished by level (§5.3): with `%arg NAME N` this is automatic, since the
macro is named. With the raw `%N` form, `%N` always means the innermost macro,
and outer parameters are unreachable without the named form.

### 7.4 Exactly one command

A macro expands to exactly one command. `%{ … %}` makes this unrestrictive while
keeping the expansion result a single CST node, so that a macro application can
appear anywhere a command can.

## Expansion

### 8.1 The algorithm

Expansion traverses the CST carrying a context of arguments, `cst option list` —
a list of optionals, not an optional list, so that a body may be traversed with
its own parameters left unbound (rule 5).

1. **Ordinary node** — recurse into children, rebuild, return.
2. **Macro application** — expand the body of the definition, with the context
   extended by the arguments in order: `%m x y` uses `<body of m>` under
   `(x, y, …)`.
3. **Imperative form** — evaluate it (§8.2–8.4).
4. **Macro parameter** — look up index `N`. If `Some v`, expand `v` and return it;
   if `None`, return the parameter unchanged, for an enclosing pass to resolve.
5. **Macro definition** —
   - expand the body with the context extended by `None` for each of the macro's
     own parameters, so the body may still refer to *outer* parameters safely;
   - check the body is well-formed with respect to the declared classes — terms
     in term positions, kinds in kind positions, and so on;
   - add the macro to the macro table.

### 8.2 Termination

Repeat until the CST contains neither macros nor imperative forms. Because a
macro may define and apply macros, this is not single-pass.

Failure conditions, stated in the correct direction:

- If a pass makes **no progress** while macros remain, expansion fails. This is
  the mutual-recursion and self-application case.
- An iteration cap bounds pathological growth and fails with the same diagnostic.

Reaching a fixed point with no macros remaining is success, not failure.

### 8.3 What "failure" means

Expansion-time failure and elaboration-time failure are different, and `%#TRY`
(§9.1) only catches the former.

- **Expansion-time** — unknown macro, wrong arity, class mismatch, non-terminating
  expansion, a failing imperative form. Reported before elaboration begins.
- **Elaboration-time** — type errors, mode errors, coverage failures in the
  *result* of expansion. Macros are gone by then; these are reported normally
  and are not catchable.

## Imperative forms

All have the syntax `%#…`. Both argument forms are `'a form` for any `'a`, i.e.
they are polymorphic over the class of their operands.

Entries marked `*` are low priority: the system is useful without them.

### 9.1 Scripting

| Form | Effect | |
|---|---|---|
| `%#TRY C1 C2` | Execute `C1`; if it fails, execute `C2`. Succeeds if either does. Short-circuiting, catching disjunction | `*` |
| `%#ECHO VALUE` | Echo a name or string literal to the console | `*` |
| `%#FAIL` | Fail. There is no `%#TRUE` — use `%{ %}` | `*` |
| `%#APPLY (NS… NAME) …` | Macro application by qualified name | |

### 9.2 Raw forms

| Form | Effect | |
|---|---|---|
| `%#SORT` | `%sort` without the modes-in-kind check (§5.4). For use inside macros that derive a `%mode` from a kind | |
| `%#BREAK` | End the current command without returning. Pointless outside the REPL | `*` |

### 9.3 Names

| Form | Effect | |
|---|---|---|
| `%#JOIN A B` | Concatenate two unqualified names | `*` |
| `%#UPPER N` | Force a name to be read as uppercase | `*` |
| `%#LOWER N` | Force a name to be read as lowercase | `*` |
| `%#QUALIFY NS N` | Qualify `N` by namespace `NS` | `*` |

`%#UPPER` / `%#LOWER` matter because case is significant in STELF: `Lcid_` and
`Ucid_` are distinct term constructors (`Cst.ml:60-61`), so a computed name must
be able to state which it is.

## Open question: `%use` versus `%#APPLY`

`%#APPLY (NS… NAME) …` above duplicates syntax that already parses:

```
%use NS.NAME (arg1 arg2 …)
```

(`Cmd.ml:517-526`) — a qualified name plus parenthesised term arguments, which is
precisely "macro application by qualified name". But the meaning of `Use_` is
contested in the tree:

| Source | Claim |
|---|---|
| `Cst.ml:235` | `(** Apply a macro *)` |
| `stelf.md:837`, `stelf.md:882` | "Module instantiation — parses, then fails" |
| `Impl.ml:883-885` | `"%use: module instantiation not yet implemented in this frontend"` |

Two readings, both defensible:

1. **`%use` is macro application.** Adopt it, drop `%#APPLY`, and correct the
   grammar reference. Cheapest — the parser branch already exists and its shape
   is right.
2. **`%use` belongs to the module system.** Keep it, and add `%#APPLY`. Costs a
   second, near-identical surface form that must be explained.

This is left open deliberately. It should be settled before either the macro
system or the module system lands, since whichever arrives second inherits the
constraint.

## Examples

### 11.1 A user-defined `%data`

The builtin `%data` (`Cmd.ml:352-397`) desugars to

```
%data NAME DECLS CMD    ⟶    %sort NAME DECLS %. %scope NAME CMD
```

The same rewrite as a macro, under a different name since `%data` is now taken:

```
%macro (lid kind cmd) datatype %{
  %sort  %arg datatype 1 %arg datatype 2 %.
  %scope %arg datatype 1 %arg datatype 3 %.
%}
```

Three classes, three parameters, three arguments:

```
%datatype vec {n nat} %{
  %term nil  vec z %.
  %term cons {n nat} nat -> vec n -> vec (s n) %.
%}
```

expanding to

```
%sort vec {n nat} %.
%scope vec %{
  %term nil  vec z %.
  %term cons {n nat} nat -> vec n -> vec (s n) %.
%} %.
```

This is the proposal's central claim in one example: a command that cost a parser
branch, a desugaring, and a test suite becomes six lines of STELF.

### 11.2 Computing a name

What the current engine cannot do — derive new syntax rather than copy it:

```
%macro (lid kind) sort-with-eq %{
  %sort %arg sort-with-eq 1 %arg sort-with-eq 2 %.
  %sort %#JOIN %arg sort-with-eq 1 eq
        {a %arg sort-with-eq 1} {b %arg sort-with-eq 1} %.
%}
```

`%sort-with-eq nat {}` declares `nat`, then declares `nateq` relating two `nat`s.
The second name exists nowhere in the arguments; `%#JOIN` computes it.

## Implementation

### 12.1 CST

- `Macro_` gains a class list: `int * string * cmd` ⟶ `class list * string * cmd`,
  the arity becoming derived rather than stored. This also removes the
  disagreement between the constructor and its doc comment (`Cst.ml:227-229`).
- A `class` type, and `'a form` — a GADT over the `Cst.t` types representing the
  syntax admitted at a given class. This is what lets rule 5's well-formedness
  check be a type-directed traversal rather than an ad-hoc one.

### 12.2 Engine

- `MACRO.apply` generalises from `C.term list` to a list of class-tagged arguments
  (`MACRO.ml:8`).
- Arity and bounds checks become real errors. They are currently `assert`s
  (`Macro.ml:56`, `Macro.ml:59`), which are erased under `-noassert` and produce
  no usable diagnostic; and the stored arity is ignored entirely (`Macro.ml:9`
  binds `_n`).
- `go_mode_term` cannot be used as written — see §14.

### 12.3 Parser

- A `%macro` branch in `Cmd.ml`'s `choice`, plus the macro-table threading of §6.
  Keyword collision is not a concern: `keyword` requires a delimiter boundary
  after the keyword body (`Lang/Parsing/Parser.ml:40-52`), which is why `%term`
  does not match the prefix of `%terminates`. Note that `keyword` prepends the
  `%` itself, so a macro branch must be written against the bare name.
- `MacroParam` gains surface syntax, so `stelf.md:498` — which lists it among
  constructors "the parser never produces" — stops being true.

### 12.4 Frontend

`Impl.ml:886` currently rejects every macro. With expansion running before
elaboration, that branch becomes unreachable and should be replaced by an
assertion that expansion has already run.

### 12.5 Locations

Error attribution after expansion is the usual risk with any rewriting pass. It is
mitigated here by an existing limitation rather than made worse by it:

> The `loc`s below are all the same outer span on purpose — `Cst.View.Cmd.review`
> (`Cst.ml:1128`) discards the location of every command constructor, so nothing
> downstream can observe a finer one.
>
> — `Cmd.ml:361-363`

Command-level locations are *already* coarse. Macros do not regress this; but
fixing `review` to preserve locations would benefit expansion and the existing
derived commands together, and is worth doing first.

## Testing

Two levels, both cheap.

- **Parse level** (`test/Parse/Cases.ml`). Round-trip each new form. This is
  where malformed input — unknown macro, wrong arity, a class mismatch, a
  parameter with no enclosing macro — should be pinned to a specific error rather
  than a generic parse failure.
- **Differential** (`test/Pal/`). Because macros are pure rewrites, write each
  example twice — once through the macro, once hand-expanded — and assert the
  results are identical. This catches desugaring drift in a way golden-output
  tests do not, and is the only test that would catch a scoping regression in
  §7.2.

The `%data` builtin gives a free first differential case: a user macro
reconstructing it (§11.1) must agree with it exactly.

## Effects and risks

- **`%` stops being a closed keyword set.** This is the largest change in the
  proposal. Today an unrecognised `%foo` is definitely an error; afterwards it is
  a macro application whose arity governs how much following text is consumed. A
  typo'd macro name can therefore produce a confusing error some distance away.
- **Non-hygiene is a deliberate hazard.** §7.2 chooses dynamic resolution because
  emitting `%scope` blocks requires it. The cost is C-preprocessor-class capture
  bugs, and no way to write a macro guaranteed not to capture.
- **Parse-time arity coupling.** §6 makes the parser depend on a table built from
  earlier in the same file. Definition-before-use is required, incremental
  reparsing gets harder, and the REPL must maintain the table across inputs.
- **Interaction with scope reopening.** `%scope` has had subtle shadowing and
  reopening semantics historically. A macro emitting `%scope` inherits every one
  of those subtleties, now generated rather than written.
- **Backwards compatibility is a non-issue.** Nothing can currently write a
  macro, and `Impl.ml:886` rejects the CST node outright, so no existing source
  changes meaning. `%use` is the sole exception, and §10 is exactly that question.
- **Mode-carrying classes are blocked** until the defect in §14 is fixed. `mode`,
  `full-mode`, and `meta` cannot be implemented before then — and those are the
  classes `%prop`/`%proof`-style macros need, i.e. the ones that motivate the
  overhaul.

## Known defects

Found while checking this proposal against the tree. Documented because they are
traps, not because they are intended.

| Where | Problem |
|---|---|
| `Cst.ml:852`, `Cst.ml:858` | `Mode.Term` lens is lossy. `view` on `ModeTermPi_ (_, d, body)` drops the mode and duplicates `body` into both slots; `review` hardcodes `Plus_`. A view→review round-trip rewrites every mode to `Plus_` |
| `Cst.ml:844-851` | `view` on `ModeTermRoot_` keeps only the head symbol and returns an empty spine; `review` rebuilds a bare `Quid_`, deleting the application's arguments |
| `Macro.ml:120-130` | `go_mode_term` performs exactly that round-trip, so macro expansion silently corrupts any `%mode` it touches. **Blocks the `mode`, `full-mode`, and `meta` classes** |
| `Cst.ml:94-95` | `MacroParam_`'s printer emits `%arg %d %d` via `Option.value ~default:0`, so `None` and `Some 0` print identically — the form does not round-trip |
| `Cst.ml:227-229` | `Macro_`'s doc comment promises a location field; the constructor is `int * string * cmd`, with no `loc` |
| `Cst.ml:235` vs `stelf.md:837` | `Use_` documented as "Apply a macro" in the CST, as module instantiation in the grammar reference. See §10 |
| `Macro.ml:56`, `Macro.ml:59` | Arity and bounds violations are `assert`s — erased under `-noassert`, unusable as diagnostics |
| `Macro.ml:9` | `apply` binds the stored arity as `_n` and ignores it; nothing checks the argument count as a whole |
| `Macro.ml:132` | `ghost` is bound but never used |
