# Stelf Syntax Design Document

> **Status:** Draft  
> **Sources:** `sketches/paeno.slf`, `src/Lang/Grammar/index.md`, Twelf reference  
> **Date:** 2026-04-07

## 1. Design Principles

Stelf's syntax departs from classic Twelf in four fundamental ways:

1. **Literate by default.** Everything outside `%`-keywords is prose. No comment syntax is needed for narrative text — the *code* is the exception, not the prose. This inverts the usual relationship where comments are annotated code; here, code is annotated text.

2. **Self-delimiting keywords.** Classic Twelf uses `.` as a universal terminator and `:` / `=` / `->` as operators within declarations. Stelf replaces these with `%`-prefixed keywords (`%sort`, `%term`, `%decl`, `%define`, `%.`, etc.) that are unambiguous even in a literate context.

3. **Uniform bracket conventions.** `{ }` always means Pi (dependent product / universal quantification), `[ ]` always means lambda (abstraction), `( )` always means application grouping. No overloading.

4. **No reserved words in the identifier namespace.** The word `type` is not reserved — it can be a user-defined constant. All Stelf keywords begin with `%`, and all implicit variables begin with `_`. Everything else is available to the user.

---

## 2. Two-Layer Architecture

Stelf syntax is organized into two layers, inspired by Isabelle/HOL:

### 2.1 Outer Language

The outer language is the document-level syntax. It handles:
- Declaration keywords (`%sort`, `%term`, `%decl`, `%define`, `%symbol`)
- Directive keywords (`%mode`, `%world`, `%total`, `%query`, etc.)
- Structural delimiters (`%.`, `%{ }`, `%[ ]`, `%( )`)
- Literate prose (everything else)

**Lexical rule:** Any token beginning with `%` is an outer-language keyword or delimiter. Everything else is either inner-language content (when inside a declaration) or prose (when outside).

### 2.2 Inner Language (Value Language)

The inner language is the term/type/kind expression language used *within* declarations. It handles:
- Pi types: `{ ... }`
- Lambda abstractions: `[ ... ]`
- Application: `( ... )` or juxtaposition
- Variables, constants, and literals

The inner language is entered when an outer keyword expects an expression body. It is exited in one of two ways:
- **`%.`** — explicitly ends the clause and returns to outer (prose) mode
- **Another top-level keyword** (e.g., `%term`, `%sort`) — implicitly ends the current clause and starts a new one without returning to prose mode

---

## 3. Outer Language: Complete Keyword Reference

### 3.1 Declaration Keywords

Each declaration keyword follows the pattern:

```
%KEYWORD NAME BODY %.
```

where `NAME` is a non-whitespace identifier and `BODY` is an inner-language expression. The declaration is terminated either by `%.` (which returns to outer/prose mode) or implicitly by the next top-level keyword (which starts a new declaration immediately).

| Keyword    | Purpose | LF Analogue | Example |
|------------|---------|-------------|---------|
| `%sort`    | Declare a type family (kind-level) | `nat : type.` | `%sort nat %.` |
| `%term`    | Declare a constructor / term constant | `zero : nat.` | `%term zero nat %.` |
| `%decl`    | Declare an inaccessible clause (no name) | `_ : ...` | `%decl add _A zero _A %.` |
| `%define`  | Define a named abbreviation | `%abbrev one = succ zero.` | `%define one (succ zero) %.` |
| `%symbol`  | Declare a symbolic shorthand (pretty-printing alias) | (none in Twelf) | `%symbol 0 zero %.` |

#### Keyword Semantics in Detail

**`%sort NAME ARGS %.`** — Declares `NAME` as a type family. The arguments (if any) are the index types of the family. The final kind is always `type` and is *never written*: `%sort` implicitly terminates at kind `type`.

```
%sort nat %.                         ≡  nat : type.
%sort add _ nat _ nat _ nat %.       ≡  add : nat -> nat -> nat -> type.
```

When `%sort` has arguments, each argument is written as an inner-language expression. Unnamed arguments use `_` as the binder name, and their types follow.

**`%term NAME TYPE %.`** — Declares a constructor or term constant. `NAME` is the constant name, `TYPE` is its type.

```
%term zero nat %.                    ≡  zero : nat.
%term succ {_ nat} nat %.           ≡  succ : nat -> nat.
```

**`%decl BODY %.`** — Declares an inaccessible clause with no user-visible name, equivalent to `_ : ...` in classic Twelf. The constant exists in the signature but cannot be referenced by name. Useful for logic programming clauses where individual names are noise.

```
%decl add _A zero _A %.             ≡  _ : add A zero A.
%decl {_ (add _A _B _C)}
      (add _A (succ _B) (succ _C)) %.
                                     ≡  _ : add A B C -> add A (succ B) (succ C).
```

Note: In `%decl`, identifiers beginning with `_` are *implicit variables* — they are universally quantified at the outermost level and inferred during reconstruction.

**`%define NAME BODY %.`** — Introduces an abbreviation. `NAME` is defined to equal `BODY`.

```
%define one (succ zero) %.          ≡  one = succ zero : nat.  (type inferred)
```

**`%symbol NAME TARGET %.`** — Declares a symbolic shorthand for pretty-printing. `NAME` becomes an alias that displays as `TARGET` but is expanded during parsing.

```
%symbol 0 zero %.
%symbol 1 one %.
```

### 3.2 Relationship Between `%sort`, `%term`, and `%decl`

The declaration keywords form a hierarchy reflecting the three levels of LF:

```
%sort    — type families (kind-level):   NAME INDICES %.  (implicit `type` at the end)
%term    — constructors / constants:     NAME TYPE %.     (named term with its type)
%decl    — inaccessible clauses:          BODY %.          (no name, equivalent to _ : ...)
%define  — abbreviations:                NAME BODY %.     (definitional equality)
%symbol  — display aliases:              NAME TARGET %.   (pretty-printing only)
```

`%sort` exists because type family declarations in LF always end with `type`, and writing it out is both redundant and confusing (since `type` *looks like* it could be a user-defined constant). `%term` declares a named constant with its type — used for constructors, functions, and named clauses. `%decl` is the inaccessible variant of `%term` — the clause exists in the signature for search but cannot be referenced by name.

In practice:
- Use `%sort` for type families (things classified by `type` / `kind`)  
- Use `%term` for constructors, functions, and named clauses (things classified by a type)
- Use `%decl` for logic-programming clauses where individual names are noise
- Use `%define` for abbreviations
- Use `%symbol` for display shorthands

### 3.3 Directive Keywords

Directives control the meta-theory and operational behavior:

| Keyword | Purpose | Example |
|---------|---------|---------|
| `%mode NAME MODES %.` | Declare mode (input/output) for a type family | `%mode add + + - %.` |
| `%world NAME BLOCKS %.` | Declare the world (context schema) | `%world add-world () %.` |
| `%total ORDER PRED CALL %.` | Request totality checking | `%total add-world _ (add _ _ C) %.` |
| `%query N BODY %.` or `%? BODY %.` | Issue a logic-programming query | `%? add zero zero zero %.` |
| `%infix{l,r} NAME PREC %.` | Declare infix operator (left/right assoc) | `%infixl + 5 %.` |
| `%prefix NAME PREC %.` | Declare prefix operator | `%prefix ~ 10 %.` |
| `%postfix NAME PREC %.` | Declare postfix operator | `%postfix ! 10 %.` |

**Mode annotations** use `+` (input), `-` (output), and `*` (unrestricted). Multiple mode declarations for the same family are allowed, enabling multi-moded relations:

```
%mode add + + - %.
%mode add - + + %.
%mode add + - + %.
```

**Totality declarations** bind an order name, a structural argument pattern, and the call pattern:

```
%total add-world _ (add _ _ C) %.
%total _ _ (add _ _ C) %.           equivalent (anonymous order, anonymous bound)
```

### 3.4 Structural Delimiters

| Delimiter | Purpose | Nesting |
|-----------|---------|---------|
| `%.` | End current clause, return to outer (prose) mode | — |
| `%{ ... %}` | Group outer declarations into a block | `%{{ ... }}` for double-nesting |
| `%[ ... %]` | Comment (hidden from processing) | `%[[ ... ]]` for double-nesting |
| `%( ... %)` | Typesetting / markup command | `%(( ... ))` for double-nesting |

**Nesting convention:** Doubling the inner bracket (`%{{ }}`, `%[[ ]]`, `%(( ))`) creates a nested scope. This avoids the need for escape sequences when the content itself contains the delimiter.

**`%.`** serves a specific role: it **ends the current clause and returns to outer (prose) mode**. It is *not* required between declarations — any top-level keyword (`%sort`, `%term`, `%decl`, `%define`, `%symbol`, `%mode`, etc.) implicitly terminates the previous clause. `%.` is only necessary when you want to return to prose between declarations, or to explicitly close the final declaration in a sequence.

In other words:
- `%term zero nat %term succ {_ nat} nat %.` — two declarations, no `%.` between them, `%.` only at the end to return to prose
- `%term zero nat %. Zero is the base case. %term succ {_ nat} nat %.` — `%.` after the first to allow prose before the second

---

## 4. Inner Language: The Value Language

The value language is used inside declaration bodies to write LF terms, types, and kinds.

### 4.1 Lexical Classes

Inside the value language, there are four lexical classes:

1. **Words** — Any sequence of non-whitespace characters excluding `%`, `{`, `}`, `(`, `)`, `[`, `]`. Words are identifiers or constants.

2. **Keywords** — Words prefixed by `%` that are *not* outer-language keywords. Currently only `%the` is an inner keyword.

3. **Implicit variables** — Words beginning with `_` (underscore). These are universally quantified at the nearest enclosing declaration scope and inferred during reconstruction.

4. **Brackets and whitespace** — Structural characters that delimit sub-expressions.

### 4.2 Expression Forms

#### Pi Types (Universal Quantification): `{ ... }`

```
{ VAR TYPE } BODY                    ≡  Π VAR:TYPE. BODY
{ _ TYPE } BODY                      ≡  TYPE → BODY  (non-dependent)
{ VAR _ } BODY                       ≡  Π VAR:_. BODY  (type omitted, inferred)
{ _ } BODY                           ≡  Π _:_. BODY  (constant pi, type inferred)
{ V1 V2 V3 TYPE } BODY              ≡  {V1 TYPE} {V2 TYPE} {V3 TYPE} BODY  (multi-bind sugar)
```

The multi-binding form `{A B C TYPE}` is syntactic sugar that expands to individual bindings. Importantly, the types may be *disjoint* after inference — the sugar only shares the syntactic annotation, not the semantic type.

#### Lambda Abstractions: `[ ... ]`

```
[ VAR ] BODY                         ≡  λVAR. BODY
[ _ ] BODY                           ≡  λ_. BODY  (constant lambda)
[ VAR TYPE ] BODY                    ≡  λVAR:TYPE. BODY
[ VAR _ ] BODY                       ≡  λVAR. BODY  (type explicitly omitted)
[ V1 V2 V3 TYPE ] BODY              ≡  [V1 TYPE] [V2 TYPE] [V3 TYPE] BODY  (multi-bind sugar)
```

**Key change from Twelf:** Types are *not allowed* inside lambda brackets in the standard syntax. The form `[VAR TYPE]` is available but the type annotation is optional and usually omitted. This differs from Twelf's `[x:A]` syntax which required the colon.

#### Application: `( ... )` and Juxtaposition

```
(f x y z)                           ≡  ((f x) y) z  (left-associative)
f x                                  ≡  f applied to x  (juxtaposition)
```

Parentheses provide explicit grouping. Without parentheses, application is by juxtaposition and follows operator precedence/fixity declarations.

#### Type Ascription: `%the`

```
%the TYPE EXPR                       ≡  EXPR : TYPE  (borrowed from Idris)
```

This replaces Twelf's infix `:` for type ascription within expressions.

### 4.3 Precedence and Associativity

Application binds tighter than Pi and Lambda. Pi and Lambda extend as far to the right as possible (they are right-associative by nature).

User-defined operators declared via `%infixl`, `%infixr`, `%prefix`, and `%postfix` participate in a numeric precedence scheme. Higher numbers bind tighter.

---

## 5. Implicit Variables and Reconstruction

Variables beginning with `_` are **implicit** — they are universally quantified at the outermost scope of the enclosing declaration and their types are inferred during reconstruction.

```
%decl add _A zero _A %.
```

Here `_A` is an implicit variable. The reconstructor infers its type as `nat` from the context (it appears as an argument to `add` and `zero`, which constrain it). The fully explicit form would be:

```
%term add/z {A nat} (add A zero A) %.
```

The convention:
- `_` alone is a wildcard (anonymous, cannot be referenced)
- `_X` is a named implicit (can be referenced multiple times within the declaration)
- `X` (no underscore) is a reference to a previously declared constant or an explicit binder

---

## 6. Literate Programming Model

### 6.1 Outer Mode (Prose)

Everything outside `%`-keywords is free-form prose. No escaping is needed for ordinary text:

```
This is prose. It can contain anything except percent signs.
%sort nat %.
The natural numbers are defined inductively.
%term zero nat %.
Zero is the base case.
%term succ {_ nat} nat %.
And successor gives us the next number.
```

### 6.2 Escaping

The `%` character is the universal escape prefix. To include a literal `%` in prose, use `%%`:

```
The success rate was 95%% in our tests.
```

### 6.3 Markup Commands: `%( ... %)`

Markup commands allow typesetting directives within literate documents:

```
%( heading{2} Arithmetic %)
Note that %( emph type %) is not reserved.
```

These are processed by the typesetting backend (e.g., Typst) and ignored by the Stelf checker.

### 6.4 Block Grouping: `%{ ... %}`

Blocks group related declarations. This is useful for structuring large developments:

```
%{
  %sort nat %.
  %term zero nat %.
  %term succ {_ nat} nat %.
%}
```

### 6.5 Comments: `%[ ... %]`

Comments are hidden from both the checker and the typesetting backend:

```
%[ This is a comment that won't appear anywhere %]
%sort nat %[ inline comment %] %.
```

---

## 7. Comparison with Classic Twelf Syntax

### 7.1 What Was Removed

| Twelf | Stelf | Rationale |
|-------|-------|-----------|
| `type` (keyword) | `%sort` | `type` is no longer reserved; kinds are implicit in `%sort` |
| `->` / `<-` | `{_ TYPE}` | Must be written out explicitly as non-dependent Pi |
| `.` (terminator) | `%.` | Strengthened to be unambiguous in literate context |
| `:` (type ascription) | `%term` / `%decl` / `%the` | Replaced by keywords at declaration level, `%the` in expressions |
| `=` (definition) | `%define` | Replaced by keyword |
| `%%` (line comment) | `%[ ... %]` | Block comments replace line comments for consistency |
| `[x : A]` (typed lambda) | `[x A]` | Colon removed; type annotation is positional |
| `(x : A)` (typed app) | `%the A x` | Type ascription uses keyword |

### 7.2 What Was Added

| Feature | Syntax | Purpose |
|---------|--------|---------|
| Literate prose | (any text outside `%`) | First-class documentation |
| Multi-binding | `{A B C nat}` / `[A B C nat]` | Concise repeated bindings |
| Symbolic aliases | `%symbol 0 zero %.` | Pretty-printing shorthands |
| Inaccessible clauses | `%decl BODY %.` | Unnamed, unreferenceable clause declarations |
| Markup commands | `%( ... %)` | Typesetting integration |
| Nested delimiters | `%{{ }}`, `%[[ ]]` | Delimiter nesting without escapes |

### 7.3 What Remains Unchanged

- `%mode`, `%world`, `%total`, `%query` (and other directives) retain their semantics
- `%infixl`, `%infixr`, `%prefix`, `%postfix` for operator fixity
- `{ }` for Pi, `[ ]` for lambda, `( )` for application grouping
- The overall LF type theory (dependent types, higher-order unification, etc.)

---

## 8. Reserved Syntax Summary

The following are reserved and cannot appear in user identifiers:

| Token | Class |
|-------|-------|
| Any word starting with `%` | Keyword or delimiter |
| Any word starting with `_` | Implicit variable |
| `{`, `}` | Pi delimiters |
| `[`, `]` | Lambda delimiters |
| `(`, `)` | Application/grouping delimiters |

Everything else — including `type`, `kind`, `->`, `<-`, `:`, `=`, `.` — is available as a user identifier.

---

## 9. Formal Grammar (EBNF)

```ebnf
(* === Outer Language === *)

document     = { prose | declaration | directive | block | comment | markup } ;

prose        = (* any characters not starting with '%' *) ;

declaration  = sort_decl | term_decl | clause_decl | define_decl | symbol_decl ;

(* Every declaration is terminated either by '%.' (returns to prose mode)
   or implicitly by the next top-level keyword. *)
sort_decl    = '%sort', NAME, { sort_arg }, [ '%.' ] ;
sort_arg     = '_', inner_expr ;                        (* unnamed index: _ TYPE *)
term_decl    = '%term', NAME, inner_expr, [ '%.' ] ;
clause_decl  = '%decl', inner_expr, [ '%.' ] ;
define_decl  = '%define', NAME, inner_expr, [ '%.' ] ;
symbol_decl  = '%symbol', NAME, inner_expr, [ '%.' ] ;

directive    = mode_decl | world_decl | total_decl | query_decl
             | infix_decl | prefix_decl | postfix_decl ;
mode_decl    = '%mode', NAME, { mode_ann }, [ '%.' ] ;
mode_ann     = '+' | '-' | '*' ;
world_decl   = '%world', NAME, '(', { NAME }, ')', [ '%.' ] ;
total_decl   = '%total', NAME, NAME, inner_expr, [ '%.' ] ;
query_decl   = ( '%query' | '%?' ), inner_expr, [ '%.' ] ;
infix_decl   = ( '%infixl' | '%infixr' | '%infix' ), NAME, NUMBER, [ '%.' ] ;
prefix_decl  = '%prefix', NAME, NUMBER, [ '%.' ] ;
postfix_decl = '%postfix', NAME, NUMBER, [ '%.' ] ;

block        = '%{', document, '%}'
             | '%{{', document, '%}}' ;
comment      = '%[', (* any *), '%]'
             | '%[[', (* any *), '%]]' ;
markup       = '%(', (* any *), '%)'
             | '%((', (* any *), '%))' ;

(* === Inner Language (Value Language) === *)

inner_expr   = pi_expr | lam_expr | app_expr | ascription | atom ;

pi_expr      = '{', binder_list, '}', inner_expr ;
lam_expr     = '[', binder_list, ']', inner_expr ;
app_expr     = '(', inner_expr, { inner_expr }, ')' ;
ascription   = '%the', inner_expr, inner_expr ;

binder_list  = '_'                                    (* constant / wildcard *)
             | IVAR, '_'                              (* variable, type omitted *)
             | WORD                                   (* variable, type inferred *)
             | WORD, inner_expr                       (* variable with type *)
             | WORD, { WORD }, inner_expr             (* multi-bind sugar *)
             ;

atom         = WORD | IVAR | '(', inner_expr, ')' ;

(* === Lexical === *)

NAME         = WORD ;
WORD         = (* non-whitespace, excluding % { } ( ) [ ] *) ;
IVAR         = '_', (* non-whitespace chars *) ;       (* implicit variable *)
NUMBER       = digit, { digit } ;
```

---

## 10. Worked Example: Peano Arithmetic

```slf
This is a comment
%sort nat %.
%term zero nat %.
%term succ {_ nat} nat %.
%define one (succ zero) %.
%symbol 0 zero %.
Symbols are shorthand
%symbol 1 one %.
This is a comment as well
%sort add
      _ nat %[ Inline comment %]
      _ nat
      _ nat
      %.

%decl add _A zero _A %.
%. Only underscores cause implicit variable names
%decl {_ (add _A _B _C)} (add _A (succ _B) (succ _C)) %.
%mode add + + - %.
%mode add - + + %.
%mode add + - + %.
%world add-world () %.
%total add-world _ (add _ _ C) %.
%? add zero zero zero %.

Issue a query

%( heading{2} arithmetic %)

Note that %( emph type %) is not reserved %.
We are free to create empty statements delimited by %%.
%sort type %.
%sort term %.

%term \ {_ {_ term} term} term
%term @ {_ term} {_ term} term
%. We don't need to add %. between terms (if we don't want to enter the outer mode)
%term -> {_ type} {_ type} term


%.

Closing thoughts
most of the other keywords are in large the same as the Twelf system
```

### Equivalent Classic Twelf

For comparison, here is what the core of the above would look like in classic Twelf syntax:

```twelf
nat : type.
zero : nat.
succ : nat -> nat.
one : nat = succ zero.

add : nat -> nat -> nat -> type.
add/z : add A zero A.
add/s : add A B C -> add A (succ A) (succ C).
%mode add +A +B -C.
%worlds () (add _ _ _).
%total {A} (add A _ _).
%query 1 * add zero zero zero.
```

---

## 11. Resolved Design Decisions

The following were previously open questions, now settled:

- **`%sort` argument syntax:** `%sort` uses only the flat `_ TYPE` pair form. Pi syntax (`{_ nat}`) is *not* accepted in `%sort` arguments — use `%term` with explicit Pi types if you need that generality.
- **Mode syntax terminator:** `%.` uniformly, like all other directives.
- **`%star` keyword:** Removed. It is not part of the Stelf syntax.
- **Implicit declaration termination:** `%.` is *not* required between declarations. Every top-level keyword implicitly terminates the previous clause. `%.` explicitly ends a clause and returns to outer (prose) mode.

## 12. Previously Open (Now Resolved)

- **`%decl` naming:** Anonymous clauses declared with `%decl` are **inaccessible** — they have no user-visible name, equivalent to `_ : ...` in classic Twelf. There is no auto-generated naming scheme; the constant simply cannot be referenced by name.
