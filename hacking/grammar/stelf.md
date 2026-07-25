# STELF Grammar

The STELF grammar changes a number of things from the Twelf grammar. This document explains those changes in prose and provides examples. For the formal grammar see [`stelf.ebnf`](stelf.ebnf).

---

## Declarations

The syntax of declarations (both for use in expressions and at the top level) is changed as follows:

1. **The colon is always elided.** `X : T` becomes `X T`. This avoids overloading such a common symbol and makes the syntax more uniform.

2. **Multiple declarations can be made at once**, if they share the same type, by surrounding the list of names in parentheses:

   ```
   [(X Y) T] Z    ≡    [X T] [Y T] Z
   (A B C) nat    ≡    A nat, B nat, C nat
   ```

   The multi-name form `(X Y) T` desugars during parsing. The CST records both names in a single `Dec_` node: `Dec_(["X"; "Y"], T, loc)`.

3. **The type is optional.** A bare name `x` (with no following type expression) produces a declaration with an omitted/inferred type. This is used in contexts like `%block` where the type may be derived from context.

### Identifier conventions in declarations

An `arg` in a declaration is either a named variable or the anonymous wildcard `_`:

| Syntax | Meaning |
|--------|---------|
| `x`    | Named variable, lowercase-initial → concrete name |
| `X`    | Named variable, uppercase-initial → metavariable / unification |
| `_x`   | Implicit argument — automatically generalised by elaboration |
| `?x`   | Meta-variable — used during interactive proof search |
| `_`    | Wildcard — anonymous, not accessible in the body |

### Qualified identifiers

Inside an expression, the form `%val(a b c)` refers to a name while **stripping all fixity properties**, forcing it to be treated as a plain applied constant. The identifier list is split: the *last* element is the name; everything before it is the module namespace path, written **outermost namespace first**, matching the dotted `outer.inner.name` order used elsewhere.

```
%val(plus)             → name "plus" with no fixity, empty namespace
%val(number nat add)   → name "add" in namespace "nat", itself inside namespace "number"
                          i.e. number.nat.add, not nat.number.add
```

This is useful when you want to pass an infix operator as a regular function argument without it being interpreted as an infix operator.

### `%val` vs `%abs`

`%abs` shares `%val`'s exact grammar (`%abs NAME`, `%abs ( NAME )`, `%abs ( PATH... NAME )` with the path outermost-first followed by the name) but resolves unqualified names differently. Both exist because a `%scope NAME cmd` session (see below) can install a case-label constant that shadows an outer/toplevel declaration sharing the same surface name — e.g. a case labeled `pi1` inside a `%scope`, shadowing a real `pi1` primitive declared earlier at the top level.

- **`%val NAME`** (and bare `NAME`, and the `%(NAME)` shorthand) is **shadow-aware**: it resolves to whichever binding is currently "on top" — the innermost open `%scope`'s version if one shadows the name, else the toplevel one.
- **`%abs NAME`** is **toplevel-first**: it prefers the current `%require` group's own toplevel declaration of NAME, bypassing any `%scope` shadow, falling back to `%val`'s shadow-aware behavior only if no toplevel binding exists.
- **Qualified forms are identical for both**: `%val ( S NAME )` and `%abs ( S NAME )` both resolve to NAME as declared inside structure `S` — `%scope` sessions install genuine, permanent Twelf structures, so qualified lookup already ignores shadowing regardless of which keyword is used.

```
%sort pi1 atom %.
%term pi1 %pi atom %-> atom %.        (* toplevel primitive *)
...
%scope wf-noassm %term pi1 ...        (* case label, shadows bare "pi1" for the rest of this %scope session *)
...
%abs pi1                              (* still the toplevel primitive *)
%val pi1                              (* the %scope's case label, since its session is still open *)
%abs ( wf-noassm pi1 )                (* the %scope's case label -- qualified, same as %val *)
```

---

## Expressions

Expression syntax has been overhauled. Both lambda and pi/forall types now use the new declaration syntax, and the grammar is split into three tiers.

### The three-tier structure

| Tier | Non-terminal | What it parses |
|------|-------------|----------------|
| Small | `expr1` | Identifiers and parenthesised expressions |
| Trailing | `expr_trail` | Lambda and pi-type bindings |
| Full | `expr` | Sequences of `expr1` optionally followed by one `expr_trail` |

This split exists for two reasons:

- **No left-recursion.** `expr` is right-to-left: it collects a flat list of atoms, then optionally attaches a trailing binder.
- **Unambiguous trailing binders.** `[x T] body` can only appear at the "end" of an expression, avoiding the classic parsing ambiguity in grammars where lambdas and application fight for the same tokens.

### Worked example

Consider: `f a [x T] b x`

1. `f`, `a` are parsed as `expr1` atoms.
2. `[x T] b x` is an `expr_trail`: it is a lambda over `b x`, and `b x` is itself a full expression (application of `b` to `x`).
3. The full expression is: atoms = `[f; a]`, trail = `Lam_(x:T, App_(b, x))`.
4. Result: `App_(App_(f, a), Lam_(x:T, App_(b, x)))`.

Another example: `[x T] y` — no atoms before the lambda, just a plain lambda term.

### Type ascription

```
%the T e
```

Explicitly ascribes type `T` to expression `e`. The first argument after `%the` is the **type** (an `expr1`), and the second is the **expression** being ascribed.

CST: `Hastype_(e, T)` — note that in the CST the expression comes first and the type second, which is the reverse of the surface syntax order.

### Pi types and function types

```
{x T} U        pi type:  x : T |- U    (dependent if x appears free in U)
{T} U          function type:  T -> U   (non-dependent)
```

The `{decl} expr` form in `expr_trail` is both a pi type and a simple arrow type depending on whether the bound variable appears in the body. The parser does not distinguish them — that is determined during elaboration.

An optional mode annotation (`%input`, `%output`, etc.) may prefix the `{`:

```
%input  {x T} U    (x is an input argument)
%output {y U} V    (y is an output argument)
```

This is only meaningful inside `%mode` declarations.

---

## Fixity Resolution

Fixity resolution comes *after* parsing, and is not encoded in the grammar. This means the parser does not need to know about operator precedence — it always produces a flat left-associative application spine, and fixity resolution rewrites it.

### The two-pass model

**Pass 1 — parsing:** All juxtaposition is treated as left-associative application. `a + b * c` is parsed as `App_(App_(App_(a, +), b), *) c`, i.e. a flat spine `a + b * c`.

**Pass 2 — fixity resolution:** Each operator in the spine is looked up in the fixity table (populated by `%prec` declarations). The spine is restructured according to declared precedences and associativities.

If there is a trailing expression (lambda or pi-type), fixity resolution first processes the atoms before it, then attaches the trail to the result.

### Declaring fixity

```
%prec %left  10 + -.
%prec %right 20 -> *.
%prec %prefix 30 ~.
```

Higher numbers bind more tightly. The fixity keywords are:

| Keyword | Meaning |
|---------|---------|
| `%left` | Left-associative infix: `a + b + c` → `(a + b) + c` |
| `%right` | Right-associative infix: `a -> b -> c` → `a -> (b -> c)` |
| `%prefix` | Prefix unary operator: `~ a` |
| `%postfix` | Postfix unary operator: `a !` |
| `%middle` | Non-associative infix: chaining is an error |
| `%none` | Remove fixity from the operator |

### Bypassing fixity

`%val(op)` strips all fixity from `op`, making it behave as an ordinary applied constant. Use this when you want to pass an infix operator as a function argument:

```
map (%val(+)) xs    (* pass + as a function, not as infix *)
```

`%abs(op)` strips fixity the same way — this is a side effect of sharing `%val`'s grammar, not a separate feature; the two keywords only differ in how they resolve unqualified names (see "`%val` vs `%abs`" above).

---

## Document Syntax

A STELF source file alternates between free-text `outer` sections and keyword-driven `cmd`s. Each command is terminated by `%.`.

```
outer ::= everything not starting with a bare `%`
file  ::= outer { cmd outer }
```

### `outer` text

`outer` is any sequence of characters that does not contain a bare `%`. It serves as documentation, comments, blank lines, or any prose — the elaborator ignores it. The escape `%%` (followed by any character) may appear inside `outer` to embed a literal percent sign.

```
This is outer text describing natural numbers.
%term nat : type.
Another outer section between commands.
%term z : nat.
```

### Command terminator `%.`

Every command ends with `%.`. The period is mandatory and serves as an unambiguous end-of-command marker, even in the presence of multi-line expressions.

### Inline command blocks `%{ ... %}`

Commands may be nested inside a `%{ ... %}` block (e.g. as the body of `%module` or `%eval`). Inside the block the same `outer { cmd outer }` structure applies:

```
%module MyMod (SigA) %{
  %term foo : nat.
  %term bar : nat -> nat.
%}.
```

---

## Commands Reference

### Definition commands

| Syntax | Purpose |
|--------|---------|
| `%term decl` | Declare a constant with a type |
| `%sort id { {decl} }` | Declare a type family (kind-level) |
| `%decl expr` | Raw elaboration-level declaration |
| `%define id expr` | Transparent definition (unfolds during type-checking) |
| `%inline id expr` | Like `%define`, but always eagerly unfolded |
| `%symbol id id` | Associate a symbolic name with an identifier |
| `%freeze id_list` | Freeze identifiers (no new clauses allowed) |
| `%thaw id_list` | Unfreeze previously frozen identifiers |

`%freeze` and `%thaw` control whether new clauses may be added to a type family. Freezing is required before coverage or totality checking.

### Mode and query commands

| Syntax | Purpose |
|--------|---------|
| `%mode id hyps` | Declare input/output polarity for a type family |
| `%? expr` | Ad-hoc REPL query: find a proof of `expr` |
| `%query n b d expr` | Logic programming query (max solutions, bound, depth) |
| `%querytabled n b d expr` | Like `%query` but with tabled (memoised) search |
| `%unique expr` | Assert `expr` has at most one inhabitant |

### World and coverage commands

| Syntax | Purpose |
|--------|---------|
| `%block id block_item*` | Define a named context schema (block label) |
| `%union id ( id* )` | Union of block labels |
| `%worlds ( id* ) expr` | Assert `expr` lives in the named world |

Coverage checking requires `%worlds` annotations. A world is built from block labels that describe what variable bindings are allowed in the context.

### Module commands

| Syntax | Purpose |
|--------|---------|
| `%module id params file` | Declare a parameterised module |
| `%use id id iparams` | Instantiate a module with concrete arguments |
| `%open id id_list` | Bring names from a module into scope |
| `%eval cmd_list` | Evaluate a command block in the current context |

### Logic commands

| Syntax | Purpose |
|--------|---------|
| `%deterministic id_list` | Mark type families as deterministic (commit to first clause) |

### Control and fixity

| Syntax | Purpose |
|--------|---------|
| `%.` | End-of-command marker |
| `%prec fixity n id_list` | Set operator fixity and precedence |
| `%{ ... %}` | Inline command block |

### REPL-only commands

These commands are only valid at the interactive REPL, not in `.elf` source files.

| Syntax | Purpose |
|--------|---------|
| `%help [topic]` | Print help |
| `%get id` | Display the value of a REPL setting |
| `%set id val` | Set a REPL configuration value |
| `%quit` | Exit the REPL |

---

## Mapping to CST Types

This table maps grammar rules to their CST constructors in `src/Common/Cst/Cst.ml` and the current parser location in `src/Fronts/Modern/Modern.ml`.

| Grammar rule | CST constructor | Parser function | Status |
|---|---|---|---|
| `ident` (lowercase-initial) | `Lcid_ of string list * string * loc` | `Modern.parse_id` | Implemented |
| `ident` (uppercase-initial) | `Ucid_ of string list * string * loc` | `Modern.parse_id` | Implemented |
| `%val(...)` qualified id | `Quid_ of string list * string * qid_form * loc` | `Modern.parse_id` | Implemented |
| `%abs(...)` qualified id (toplevel-first) | `Quid_ of string list * string * qid_form * loc` | `Modern.parse_id` | Implemented |
| `expr1` (parenthesised) | (delegates to inner `expr`) | `Modern.parse_expr1` | Implemented |
| `expr_trail` lambda `[d] e` | `Lam_ of decl * term` / `Cst.Term.lam` | `Modern.parse_expr_trail` | Implemented |
| `expr_trail` pi `{d} e` | `Pi_ of decl * term` / `Cst.Term.pi` | `Modern.parse_expr_trail` | Implemented |
| `expr` application spine | `App_ of term * term` / `Cst.Term.app` | `Modern.parse_expr_app` | Implemented |
| `%the T e` | `Hastype_ of term * term` / `Cst.Term.has_type` | `Modern.parse_expr` | Implemented |
| `decl` single | `Dec_ of string option list * term * loc` | `Modern.parse_decl` | Implemented |
| `decl` multi `(x y) T` | `Dec_ of string option list * term * loc` | `Modern.parse_decl` | Implemented |
| `arg` wildcard `_` | `None` in the names list | `Modern.parse_arg` | Implemented |
| `mode` annotation | `Cst.mode` = `Plus_ \| Star_ \| Minus_ \| Minus1_` | `Modern.parse_mode` | **Stubbed** |
| `%mode` declaration | `Cst.modeDec` = `ModeDec_` | `Modern.parse_mode_dec` | **Stubbed** |
| `sigexp` | `Cst.sigexp` = `TheSig_ \| SigId_ \| WhereSig_` | `Modern.parse_sigexp` | **Stubbed** |
| `inst` | `Cst.inst` = `ConInst_ \| StrInst_` | `Modern.parse_inst` | **Stubbed** |
| `%query` / `%?` | `Cst.query` = `Query_` | `Modern.parse_query` | **Stubbed** |
| `%define` | `Cst.define` = `Define_` | `Modern.parse_define` | **Stubbed** |
| `%prec fixity` | `int` (precedence level) | `Modern.parse_fixity` | **Stubbed** |
| `%block` / `%worlds` | `Cst.ConDec.block_decl` / `block_def` | — | **Missing** |
| theorem syntax (`%term`, `%sort`) | `Cst.Cmd.term` / `Cst.Cmd.sort` | — | **Missing** |
| `%module` / `%use` / `%open` | `Cst.Struct.*` | `Modern.parse_struct_dec` | **Stubbed** |

"Stubbed" means the function exists in `Modern.ml` but contains `assert false`. "Missing" means there is no parser entry point yet — these should be added to `Modern.ml`.

---

## Parser Implementation Status

The modern parser lives in `src/Fronts/Modern/Modern.ml` and uses Angstrom-based combinators from `src/Lang/Parsing/Parser.ml`.

**Fully implemented:**
- All expression parsing (`expr`, `expr1`, `expr_trail`, application)
- Declaration parsing (single and multi-name)
- Identifier parsing including `%val(...)` and `%abs(...)` qualified forms

**Stubbed (`assert false`):**
- Mode syntax (`parse_mode`, `parse_mode_dec`)
- Module/signature syntax (`parse_sigexp`, `parse_inst`, `parse_sigdef`, `parse_struct_dec`)
- Fixity declarations (`parse_fixity`)
- Query/define/solve commands (`parse_query`, `parse_define`, `parse_solve`)
- Helper grouping parsers (`parse_group`, `parse_parens`, `parse_braced`, `parse_bracketed`)
- Top-level `run` function

**Not yet started:**
- World commands (`%block`, `%union`, `%worlds`)
- Theorem commands (`%term`, `%sort`)
- REPL command dispatch
- `%prec` fixity declarations
- `cmd_list` / `file` top-level structure

The legacy frontend at `src/frontend/` is complete and handles all of the above; it can serve as a reference implementation for the missing modern parser rules.
