# Modern STELF Grammar

A reference BNF for the **modern** STELF surface syntax — the variant
parsed by `src/Fronts/Modern/Modern.ml` and `src/Fronts/Modern/Cmd.ml`,
and exercised by `test/Parse/Cases.ml`.

This is **not** legacy Twelf syntax. The legacy frontend
(`src/frontend/Parse*.ml`) accepts Twelf-style declarations
(`c : A.`, `[x:A] M`, `{x:A} B`, `%mode +x -y`, trailing `.`). That
grammar is out of scope here.

This document is intended to:

1. Serve as a human-readable spec for writing and reading STELF code.
2. Drive a future tree-sitter implementation. A design-notes appendix
   covers tree-sitter-specific concerns; the body of the document is
   pure BNF + commentary.

Notational conventions:

- `lowercase` names are non-terminals.
- `"foo"` is a literal terminal.
- `x*`, `x+`, `x?` are Kleene closure / one-or-more / optional.
- `(* ... *)` are grammar-level comments.
- All productions describe **modern STELF**, as accepted by the parser
  on the `dev` branch at the time of writing.

---

## 1. Overview

STELF source is a stream of **commands**. Every command and every
reserved word begins with `%`. Everything else — `nat`, `succ`, `+`,
`<=`, `add/zero`, `_X` — is an identifier. There are no statement
terminators; commands are delimited by the *start* of the next `%`-word.

The only punctuation tokens are `(` `)` `{` `}` `[` `]` `%`. Whitespace
separates identifiers and otherwise has no meaning.

A small example:

```stelf
%sort nat
%term zero nat
%term succ {_ nat} nat

%sort add {_ nat} {_ nat} {_ nat}
%term add/zero {y nat} add zero y y
%term add/succ {x nat} {y nat} {z nat} {_ add x y z}
              add (succ x) y (succ z)

%mode {%in x nat} {%in y nat} {%out z nat} add x y z
%worlds () (add _ _ _)
%total N (add N _ _)
```

---

## 2. Lexical structure

```bnf
(* Whitespace is space, tab, and newline; never significant.       *)
ws         ::= ( " " | "\t" | "\n" )*

(* The only punctuation. Everything else is an identifier char.    *)
delim      ::= "(" | ")" | "{{" | "}}" | "{" | "}" | "[" | "]" | "%" | ws | EOF

(* An identifier is any non-empty run of non-delimiter chars.      *)
ident      ::= ident-char+
ident-char ::= <any character except space, tab, newline, '(', ')',
                '{', '}', '[', ']', '%'>

(* A keyword is '%' immediately followed by an identifier body
   AND a word boundary. The boundary check is what prevents
   '%term' from being mistaken for the prefix of '%terminates'.   *)
keyword s  ::= "%" s &(delim)             (* lookahead, not consumed *)

(* Natural number literals — used by %query bounds and %prec.     *)
nat        ::= [0-9]+
```

Consequences worth knowing:

- `=`, `<`, `>`, `<=`, `>=`, `+`, `*`, `:`, `:=`, `add/zero`, `_X` are
  all valid identifiers. None are reserved.
- Identifier *case* is decided by the first character, not by the
  lexer:
  - leading `_` or name mentioned in scope inside `{{A B...}}` → **uppercase** (used as a metavariable),
  - anything else → **lowercase** (a constant).
- **Comments and strings.** A `%` followed by whitespace (and not itself
  the second `%` of an escape) begins a **line comment** to end of line;
  these are recognised anywhere whitespace is allowed, in both the outer
  (document) and inner (term) contexts. `%[ ... %]` (and `%[[ ... %]]`, with
  *n* opening brackets closed by *n* closing brackets) is a **string**: the
  lexer scans raw text to the matching close and yields a single token. It
  lexes identically in either context — in the outer context a bare string
  is ignorable prose (this replaces the old `%{ ... }%` block comment), in a
  term it is a string value. There is **no** multi-line comment form: `%[ ...
  %]` in a term is a value, not a discarded comment. `%%X` is an **escape**
  that turns the next character `X` into a literal identifier character (so
  `%%%` is a literal `%`, and `%%%term` is the identifier `%term`, not the
  keyword) — it does *not* begin a comment.

---

## 3. Top-level command stream

```bnf
program     ::= ( outer-text command )* outer-text
outer-text  ::= <any chars not '%'>*       (* skipped between commands *)

command     ::= stop
              | term-cmd
              | mode-cmd | covers-cmd
              | module-cmd | use-cmd | open-cmd | eval-cmd
              | sort-cmd | block-cmd | union-cmd | worlds-cmd
              | freeze-cmd | thaw-cmd | deterministic-cmd
              | name-cmd | symbol-cmd | inline-cmd
              | define-cmd | solve-cmd | decl-cmd
              | query-cmd | qtab-cmd | adhoc-query-cmd
              | unique-cmd
              | total-cmd | terminates-cmd | reduces-cmd
              | prec-cmd
              | repl-cmd

stop        ::= "%."
```

The complete keyword inventory is enumerated in §13.

---

## 4. Terms

The term grammar is the heart of STELF.

```bnf
expr        ::= ascription
              | arrow-chain
              | backarrow-chain
              | expr-app

ascription  ::= "%the" expr1 expr             (* ascribe: body : type *)

(*  %-> A %-> B %-> C    ==>   {_ A} {_ B} C
    The '%->' between arguments is optional after the first.        *)
arrow-chain ::= "%->" expr1 ( "%->"? expr1 )+

(*  %<- A %<- B %<- C    ==>   {_ C} {_ B} A
    Like arrow-chain but the *first* argument is the body.          *)
backarrow-chain
            ::= "%<-" expr1 ( "%<-"? expr1 )+

(* Application is juxtaposition.  A trailing lambda/Pi binder may
   follow the last argument:    f x y [w] w    parses as
                                f applied to x, y, and [w] w        *)
expr-app    ::= expr1+ expr-trail?
              | expr-trail                    (* trailing-only is ok *)

expr-trail  ::= "[" decl "]" expr             (* lambda abstraction *)
              | "{" decl "}" expr             (* dependent product  *)
              | "{{" ident+ "}}" expr             (* List of names that should be treated as uppercase in expr *)

(* "Small" expression: legal as an application argument or inside
   a parenthesised expression.  No top-level binders, ascriptions,
   or arrow chains here.                                            *)
expr1       ::= atom
              | "(" expr ")"

atom        ::= ident                         (* upper- or lower-case *)
              | qualified

qualified   ::= "%val" ident                  (* unqualified, shadow-aware   *)
              | "%val" "(" ident+ ")"         (* dotted-path, shadow-aware   *)
              | "%abs" ident                  (* unqualified, toplevel-first *)
              | "%abs" "(" ident+ ")"         (* dotted-path, identical to %val *)
```

Notes:

- `expr-app`'s `expr1+ expr-trail?` is what lets `f x [y] y` and
  `f {x nat} x` parse cleanly.
- An atom is upper- or lowercase based on the *first character* of
  the identifier (§2). `_X` and `Foo` are uppercase; `nat`, `+`, `<=`
  are lowercase.
- A parenthesised expression `( expr )` may contain anything, including
  another binder chain.
- `%val NAME` and `%abs NAME` share this grammar but resolve differently
  when NAME is unqualified and ambiguous (e.g. shadowed by an open
  `%scope`): `%val` prefers the innermost/most-recently-shadowed binding,
  `%abs` prefers the current `%require` group's own toplevel declaration,
  falling back to `%val`'s behavior if there is none. Both forms resolve
  identically once qualified with a namespace path — see
  `hacking/grammar/stelf.md`'s "Qualified identifiers" section for the full
  explanation and worked examples.

### 4.1 Test-suite examples (from `test/Parse/Cases.ml:31-72`)

| Surface | Production |
|---|---|
| `nat` | `atom` |
| `succ zero` | `expr-app` |
| `succ (succ zero)` | `expr-app` with parenthesised arg |
| `[x] x` | `expr-trail` (lambda) |
| `{x} x` | `expr-trail` (Pi) |
| `%the nat zero` | `ascription` |
| `succ zero [x] x` | `expr-app` with trailing lambda |
| `f {x} x [y] y` | nested trailing binders |
| `_X` | uppercase atom |
| `%val ( x y )` | qualified |
| `%val +` | qualified (single, including symbolic ident) |
| `%abs ( x y )` | qualified, identical resolution to `%val ( x y )` |
| `%abs x` | qualified, toplevel-first resolution (differs from `%val x`) |
| `f [x nat] [y nat] x` | nested lambdas with typed binders |
| `f {p {_ nat} nat} z` | Pi with a nested-Pi binder type |

---

## 5. Declarations (binders)

A **declaration** is the `x : A` or `(x y) : A` slot that appears inside
`[...]` and `{...}` binders, inside `%term`, `%mode`, etc. In modern
STELF there is *no* colon — the type follows the name(s) directly.

```bnf
decl  ::= "(" arg+ ")" expr?     (* grouped names, optional type     *)
        | arg expr?              (* single name,  optional type      *)

arg   ::= "_" | ident
```

Examples (from `test/Parse/Cases.ml:51-58`):

| Surface | Meaning |
|---|---|
| `x nat` | one name, one type |
| `(x y) nat` | two names sharing a type |
| `x` | untyped binder |
| `(x y)` | untyped grouped binder |
| `_ nat` | anonymous, typed |
| `_` | anonymous, untyped |

---

## 6. Modes

A mode marker classifies a binder position as input / output.

```bnf
mode      ::= "%in"           (* + : input,    must be ground         *)
            | "%out"          (* - : output                           *)
            | "%out1"         (* -1: strict output (at most one)      *)
            | "%star"         (* * : either, no constraint            *)

(* A mode declaration mixes braced full-form and trailing spine form.
   The braced binders come *first*, then the head expression, then
   trailing bare modes for the head's spine.                          *)
mode-dec  ::= ( "{" mode decl "}" )* expr mode*
```

The three surface shapes (from `test/Parse/Cases.ml:111-117`):

```stelf
(* full form: every argument has its mode in a braced binder *)
%mode {%in x nat} {%in y nat} {%out z nat} add x y z

(* spine form: bare modes follow the predicate *)
%mode add %in %in %out

(* mixed: leading braced binders, then trailing spine *)
%mode {%in x nat} {%in y nat} add x y %out
```

Mode declarations appear in `%mode` and `%covers` commands.

---

## 7. Block / world / union

```bnf
(* {decl} is universal/Pi-bound; [decl] is existential/some-bound. *)
block-item ::= "{" decl "}"
             | "[" decl "]"

block-cmd  ::= "%block" ident block-item*

union-cmd  ::= "%union" ident "(" ident+ ")"

worlds-cmd ::= "%worlds" "(" ident* ")" expr
```

Examples (`test/Parse/Cases.ml:118-133`):

```stelf
%block test { x nat }
%block test { x nat } { y bool }
%block test [x nat]
%block test [(x y) nat]
%union test (nat bool)
%worlds () (add _ _ _)
%worlds (N) (add N _ _)
```

---

## 8. Termination orders

`%total` and `%terminates` take an *order* and a list of call patterns.
Orders compose:

```bnf
order       ::= id-list                       (* varg: a flat list  *)
              | "[" order+ "]"                (* simultaneous       *)
              | "{" order+ "}"                (* lexicographic      *)

id-list     ::= ident
              | "(" ident+ ")"

(* The parenthesised form lets you give a tuple of orders, one per
   mutually-recursive predicate.                                    *)
order-list  ::= "(" order+ ")"
              | order

total-cmd       ::= "%total"       order-list expr1+
terminates-cmd  ::= "%terminates"  order-list expr1+
```

Examples (`test/Parse/Cases.ml:135-153`):

```stelf
%total N (add N _ _)
%total (N1 N2) (add N1 _ _) (mul N2 _ _)
%terminates N (add N _ _)
%terminates [A B] max A B                  (* simultaneous *)
%terminates {A B} max A B                  (* lexicographic *)
%terminates {A [B C] F} (max A (max B C))  (* nested *)
%terminates ({A [B C] G} [D E] F) (max A (max B C) max D (max E C))
```

---

## 9. Reduces

`%reduces` declares a size relation between argument positions:

```bnf
reduces-rel ::= "<=" | ">=" | "<" | ">" | "="
reduces-cmd ::= "%reduces" reduces-rel expr1+
```

The relations are *identifiers* lexically (§2), but the parser tries
the two-character forms before the one-character forms so `<=` is not
read as `<` followed by `=`.

Examples (`test/Parse/Cases.ml:162-169`):

```stelf
%reduces =  X Y add X Y zero
%reduces <  X Y add X Y zero
%reduces >  X Y add X Y zero
%reduces >= X Y add X Y zero
%reduces <= X Y add X Y zero
```

---

## 10. Signatures, structures, modules

TODO

---

## 11. Queries, defines, solves

```bnf
bound          ::= "_" | nat            (* '_' means unbounded *)

query-cmd      ::= "%query"       bound bound bound expr
qtab-cmd       ::= "%querytabled" bound bound bound expr
adhoc-query    ::= "%?" expr

define-cmd     ::= ( "%define" | "%def" ) ( ident | "_" ) expr1 expr

solve-cmd      ::= "%solve" expr
decl-cmd       ::= "%decl"  expr
inline-cmd     ::= "%inline" ident expr
unique-cmd     ::= "%unique" expr
```

`%def` is an accepted synonym for `%define` (Cmd.ml:84).

Examples (`test/Parse/Cases.ml:155-160, 100-110`):

```stelf
%? nat
%? add zero zero zero
%query _ _ 1 add zero zero zero

%def not ({_ prop} prop) ([a] imp a false)
%def eq_i (pf (eq _A _A)) prop
```

---

## 12. Sorts, terms, names, fixity, etc

```bnf
sort-cmd        ::= "%sort" id-list ( "{" decl "}" )*
term-cmd        ::= "%term" decl

freeze-cmd      ::= "%freeze"        id-list
thaw-cmd        ::= "%thaw"          id-list
deterministic-cmd
                ::= "%deterministic" id-list

name-cmd        ::= "%name"   ident
prose-cmd       ::= "%prose"  ident
symbol-cmd      ::= "%symbol" ident ident
covers-cmd      ::= "%covers" mode-dec

fixity-kw       ::= "%left" | "%right" | "%prefix"
                  | "%postfix" | "%middle" | "%none"
prec-cmd        ::= "%prec" fixity-kw nat id-list

(* REPL-only commands.                                              *)
repl-cmd        ::= "%quit"
                  | "%help" ident?
                  | "%get"  ident
                  | "%set"  ident ident
                  | "%version"
```

Note on `%sort`: the parser accepts `%sort nat` (a bare id-list) or
`%sort (nat bool)` (a grouped id-list of mutually-defined sorts), each
optionally followed by indexed parameter binders such as
`{_ nat} {_ nat}`. The test suite covers both shapes
(`test/Parse/Cases.ml:73-86`).

---

## 13. Command reference (alphabetical)

The full list of `%`-prefixed commands recognised by `Cmd.ml`. Each
entry shows the BNF, the source line in `Cmd.ml`, and (where one
exists) a test-suite example.

| Command | Body | Cmd.ml | Example |
|---|---|---|---|
| `%.` | — | 35 | (end-of-input marker) |
| `%?` | `expr` | 53 | `%? add zero zero zero` |
| `%block` | `ident block-item*` | 144 | `%block test { x nat } [y bool]` |
| `%covers` | `mode-dec` | 265 | `%covers add %in %in %out` |
| `%decl` | `expr` | 92 | `%decl (eq nat nat)` |
| `%define` / `%def` | `(ident\|"_") expr1 expr` | 84 | `%def not ({_ prop} prop) ([a] imp a false)` |
| `%deterministic` | `id-list` | 168 | `%deterministic (add)` |
| `%eval` | `"%{" command* "%}"` | 192 | `%eval %{ %? nat %}` |
| `%freeze` | `id-list` | 115 | `%freeze (nat)` |
| `%get` | `ident` | 230 | `%get chatter` |
| `%help` | `ident?` | 219 | `%help mode` |
| `%inline` | `ident expr` | 99 | `%inline succ_z (succ zero)` |
| `%mode` | `mode-dec` | 77 | `%mode {%in x nat} add x %out` |
| `%module` | `ident "(" ident* ")" "%{" command* "%}"` | 68 | `%module Nat () %{ %sort n %}` |
| `%name` | `ident` | 272 | `%name addition` |
| `%open` | `ident id-list` | 184 | `%open M (succ zero)` |
| `%prec` | `fixity-kw nat id-list` | 199 | `%prec %left 5 (+)` |
| `%prose` | `ident` | 393 | `%prose highlightHint` |
| `%query` | `bound bound bound expr` | 46 | `%query _ _ 1 add zero zero zero` |
| `%querytabled` | `bound bound bound expr` | 39 | `%querytabled _ _ _ p` |
| `%quit` | — | 216 | `%quit` |
| `%reduces` | `reduces-rel expr1+` | 279 | `%reduces < X Y add X Y zero` |
| `%set` | `ident ident` | 237 | `%set chatter 3` |
| `%solve` | `expr` | 209 | `%solve add zero zero zero` |
| `%sort` | `id-list ( "{" decl "}" )*` | 129 | `%sort prop {_ nat} {_ nat}` |
| `%symbol` | `ident ident` | 107 | `%symbol plus +` |
| `%term` | `decl` | 137 | `%term succ {_ nat} nat` |
| `%terminates` | `order-list expr1+` | 257 | `%terminates {A B} max A B` |
| `%thaw` | `id-list` | 122 | `%thaw (nat)` |
| `%total` | `order-list expr1+` | 249 | `%total N (add N _ _)` |
| `%union` | `ident "(" ident+ ")"` | 152 | `%union test (nat bool)` |
| `%unique` | `expr` | 60 | `%unique nat` |
| `%use` | `ident ident "(" ident* ")"` | 175 | `%use M N ()` |
| `%version` | — | 245 | `%version` |
| `%worlds` | `"(" ident* ")" expr` | 160 | `%worlds () (add _ _ _)` |

Three additional command keywords expected from the CST but **not**
currently parsed by `Cmd.ml` (gaps, listed in §15): `%abbrev`,
`%trustme`, `%subord`.

---

## 14. End-to-end examples

```stelf
(* Peano naturals *)
%sort nat
%term zero nat
%term succ {_ nat} nat

(* Addition relation, mode-directed *)
%sort add {_ nat} {_ nat} {_ nat}
%term add/zero {y nat} add zero y y
%term add/succ {x nat} {y nat} {z nat} {_ add x y z}
              add (succ x) y (succ z)

%mode {%in x nat} {%in y nat} {%out z nat} add x y z
%worlds () (add _ _ _)
%total N (add N _ _)

(* Multiplication, expressed in terms of addition *)
%sort mul {_ nat} {_ nat} {_ nat}
%term mul/zero {x nat} mul x zero zero
%term mul/succ {x nat} {y nat} {z nat} {z' nat}
              {_ mul x y z} {_ add y z z'}
              (mul (succ x) y z')

(* Sample queries *)
%? nat
%? add zero zero zero
%query _ _ 1 add zero zero zero

(* Reduction relation declaration *)
%reduces <= X Y add X Y zero
```

---

## 15. Gaps and TODOs

Things the modern parser does **not** currently handle, deliberately
omitted from the BNF above:

- **Comments**. The modern lexer recognises `%`-whitespace line
  comments (both contexts) and `%[ ... %]` strings (ignorable prose in
  the outer context, a value in a term); it has **no** multi-line
  comment form. `%%X` is an escape, not a comment. The retired
  `%{ ... }%` block comment is replaced by `%[ ... %]`; `%{`/`%}`
  remain command-block delimiters (`%eval`, `%module`). See §2.
- **String literals**. `Modern.parse_text` (`Modern.ml:297-301`)
  defines a `%"..."%` literal form, but no command currently calls
  it. The `Scon_` CST node it would build is unreachable from
  surface syntax today.
- **Namespace-qualified raw identifiers**. The CST supports a `namespace`
  list (e.g. `Mod.Sub.foo`), but the modern parser only produces
  qualified names via `%val` (§4). Direct dotted-path identifiers
  are not parsed.
- **`%abbrev`, `%trustme`, `%subord`**. Present in the legacy parser
  and in the original Twelf, but the modern `Cmd.ml` `choice` block
  does not include them. They are reserved for future work.
- **`Foreign` / `Internal` term constructors**. Listed in
  `Cst.View.Term.u` (`Cst.ml:516-517`) but `review` raises `Lacking`
  on them — they have no surface syntax.

---

## 16. Appendix: tree-sitter design notes

This appendix gathers observations relevant to implementing STELF in
[tree-sitter](https://tree-sitter.github.io/). It does **not** include
a `grammar.js`; it is meant to surface every place where naively
translating the BNF will go wrong.

### 16.1 Token model

The lexer is in `src/Lang/Parsing/Parser.ml:12-43`. Key rules:

- **`whitespace`** consumes only space, tab, newline.
- **`ident1`** is `take_while1` of every character *not* in
  `" \t\n(){}[]%"`. In tree-sitter terms:

  ```
  identifier : /[^ \t\n(){}\[\]%]+/
  ```

- **`keyword s`** prepends `%`, then *peeks* the next character and
  requires it to be a delimiter — one of `" \t\n(){}[]%"` or EOF. This
  is what stops `%term` from matching the prefix of `%terminates`.
  In tree-sitter:

  ```js
  function kw(s) {
    return token(seq('%', s, /(?=[\s(){}\[\]%]|$)/));
  }
  ```

  The lookahead must be a zero-width regex; it cannot be a token.

### 16.2 Identifier vs keyword

Only `%`-prefixed words are ever reserved. Bare identifiers in
expression position can be arbitrary non-delimiter strings: `nat`,
`+`, `<=`, `==>`, `add/zero`, `_X` are all the same token class.

Do **not** split identifiers into "alphanumeric" and "symbolic" at
the lexer — STELF does not make that distinction.

### 16.3 Uppercase vs lowercase identifier

The first-character rule (`_` or `A`–`Z` → uppercase) is enforced in
the *consumer*, not the lexer (`Modern.ml:194-200`). Two options:

- **Single token, tag in the rule.** Keep one `identifier` token and
  let the consuming grammar rules (or downstream tooling) inspect the
  first char. Recommended — preserves symbol identifiers like `+`.
- **Split tokens.** Define `lower_ident : /[^A-Z_ \t\n(){}\[\]%][^...]*/`
  and `upper_ident : /[A-Z_][^...]*/`. Cleaner for highlighting but
  forces every operator-only ident (e.g. `+`) onto one side.

### 16.4 Dynamic `%prec`

`Modern.ml:34-47, 121-156` shows that `%prec` mutates a `Hashtbl` of
local fixities at parse time, and the parser then performs an
operator-precedence shift-reduce on the application list. This is
intrinsically stateful and **not** expressible in tree-sitter's static
grammar.

Recommendation: parse application as a flat sequence
(`seq($.expr1, repeat1($.expr1))`) and defer operator resolution to a
post-tree pass (a separate elaboration step that reads `%prec`
declarations from the same file). This matches how `Modern.ml` itself
defers all elaboration to `Recon`.

### 16.5 Arrow / backarrow chains

```ocaml
keyword "->" *> ... sep_by1 (option () @@ keyword "->") (parse_expr1 ())
```

(`Modern.ml:241-247`) — the separator is **optional** after the first
occurrence. The chain is greedy and right-folds into a `{_ A} ... B`
Pi-type.

Tree-sitter shape:

```js
arrow_chain : seq('%->', $.expr1, repeat(seq(optional('%->'), $.expr1)))
```

### 16.6 Trailing binders in application

`expr-app ::= expr1+ expr-trail?` means a lambda or Pi can syntactically
appear at the tail of an application — the binder is not in
parentheses. `f x y [w] w` is `(f x y) (lambda w. w)`.

This is the reason `expr-trail` is split from `expr1`: a trailing
binder is too greedy for a small-expression position.

### 16.7 Statement boundary

Outer text between commands is *anything not starting with `%`*
(`Cmd.ml:16`: `skip_while (fun c -> c <> '%')`). Practical model in
tree-sitter:

- Mark `%`-keyword tokens as the only valid command starters.
- An external scanner (or a token rule with extras) absorbs runs of
  non-`%` characters between commands.

### 16.8 Block delimiters

`keyword "{"` and `keyword "}"` prepend `%`, so command-list blocks
(`%module`, `%eval`) are delimited by `%{` and `%}`, not bare braces.
Bare `{`/`}` are reserved for Pi binders inside terms.

### 16.9 Comments and strings

The modern lexer recognises:

- `%`-whitespace **line comments** (to end of line), in both the outer
  and inner contexts. Model these as `extras` so they are absorbed
  wherever whitespace is allowed.
- `%[ ... %]` / `%[[ ... %]]` **strings** (*n* opening brackets close
  with *n* closing brackets); a single token holding raw text. In the
  outer context a bare string is ignorable prose; in a term it is a
  value. There is no multi-line comment form.
- `%%X` **escape**: the next character `X` becomes a literal identifier
  character (`%%%` = literal `%`, `%%%term` = identifier `%term`). Not a
  comment.

`%{ ... %}` is **not** a comment — `%{`/`%}` are command-block
delimiters (`%eval`, `%module`). The old `%{ ... }%` block comment is
retired in favour of `%[ ... %]`.

### 16.10 Keyword inventory for tree-sitter

The full set of `%`-keywords accepted by the modern parser. Split into
command-level keywords (only valid at command position) and
in-expression keywords (only valid inside `expr`/`mode-dec`/`sigexp`).

**Command-level** (from `Cmd.ml`):

`%.` `%?` `%block` `%covers` `%decl` `%def` `%define`
`%deterministic` `%eval` `%freeze` `%get` `%help` `%inline` `%mode`
`%module` `%name` `%open` `%prec` `%query` `%querytabled` `%quit`
`%reduces` `%set` `%solve` `%sort` `%symbol` `%term` `%terminates`
`%thaw` `%total` `%union` `%unique` `%use` `%version` `%worlds`
`%{` `%}`

**In-expression** (from `Modern.ml`):

`%the` `%val` `%abs` `%->` `%<-` `%in` `%out` `%out1` `%star` `%where`
`%left` `%right` `%prefix` `%postfix` `%middle` `%none`

### 16.11 Reduces operators

`%reduces` accepts `<=`, `>=`, `<`, `>`, `=` (`Modern.ml:457-465`).
These are **identifiers**, not keywords — `Modern.ml` matches them
with `token`, not `keyword`, and the order of alternatives matters
(two-char forms first). A tree-sitter grammar can either:

- match them as a fixed set of named alternatives inside `reduces-cmd`
  (recommended — gives them their own syntax-tree node);
- accept any identifier in that position and validate downstream.
