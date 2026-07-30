# STELF Syntax Reference

STELF is a redesign of the [Twelf](http://twelf.org/) surface syntax over the same
LF logical framework. This document describes the language **as implemented**.

> **The parser is the specification.** Every claim here cites the code that
> enforces it. Where a doc comment elsewhere in the tree contradicts the parser,
> the parser is right and the comment is a bug — §10.2 lists the ones known at the
> time of writing. If you change `Modern.ml`, `Cmd.ml` or `Parser.ml`, change this
> file.

For machine-readable forms see [`stelf.ebnf`](stelf.ebnf) (productions) and
[`tokens.md`](tokens.md) (token tables, for lexers and highlighters).

## How to read this

Every construct is tagged with its relationship to Twelf:

| Tag | Meaning |
|---|---|
| `[new]` | No Twelf equivalent |
| `[changed]` | Same concept, different spelling |
| `[shared]` | Same as Twelf |
| `[absent]` | Twelf has it, STELF does not |

Jump to [§9 Migrating from Twelf](#9-migrating-from-twelf) for the summary tables.

**Where the implementation lives:**

| Layer | File |
|---|---|
| Tokens, escapes, text literals, comments | [`src/Lang/Parsing/Parser.ml`](../../src/Lang/Parsing/Parser.ml) |
| Expressions, binders, fixity resolution | [`src/Fronts/Modern/Modern.ml`](../../src/Fronts/Modern/Modern.ml) |
| Commands | [`src/Fronts/Modern/Cmd.ml`](../../src/Fronts/Modern/Cmd.ml) |
| Printer — the inverse, must stay in sync | [`src/Pretty/Lex.ml`](../../src/Pretty/Lex.ml), [`src/Pretty/Pretty.ml`](../../src/Pretty/Pretty.ml) |
| Scope / open / require semantics | [`src/Fronts/Pal/Impl.ml`](../../src/Fronts/Pal/Impl.ml), [`src/Fronts/Pal/Loader.ml`](../../src/Fronts/Pal/Loader.ml) |
| Accepted-syntax corpus | [`test/Parse/Cases.ml`](../../test/Parse/Cases.ml), [`test/STELF/`](../../test/STELF/) |

---

## 1. Document structure

### 1.1 Files are literate by default `[new]`

A source file is a sequence of commands separated by arbitrary prose. Everything
that is not a command is discarded: `skip_outer` skips forward to the next `%`
(`Cmd.ml:32-58`), and the file parser is just `outer { command outer }`
(`Cmd.ml:692`). No comment marker is needed around narrative text.

```
# Natural numbers

We start with the type of naturals and its two constructors.

%sort nat %.
%term zero nat %.
%term succ {_ nat} nat %.
```

The Markdown above is not commented out — it is simply not a command, so nothing
looks at it.

### 1.2 `%.` is a separator, not a terminator `[changed]`

Twelf terminates every declaration with `.`. STELF's `%.` (`Cmd.ml:220-226`) is a
no-op at install time (`Impl.ml:557`) and is **optional between two commands**:

```
%sort nat
%term zero nat        %; legal — the next % ends the previous command
```

A declaration ends at the next unescaped `%`, because identifiers cannot contain
one (§2.1). But `%.` is **required before prose**, which does not start with `%`
and would otherwise be swallowed as application arguments:

```
%sort nat %.
Now the constructors.
%term zero nat %.
```

Without that first `%.`, `Now the constructors.` parses as four more arguments to
`%sort`, and the errors say so:

```
Undeclared identifier the
Undeclared identifier constructors.
Ambiguous reconstruction
```

Note that the second name is `constructors.` **with the full stop included** — a
bare `.` is an ordinary identifier character (§2.1), and `%.` is the keyword.
Corpus style is to write `%.` after every declaration; do that.

### 1.3 Command blocks `%{ … %}` `[changed]`

`%{ … %}` groups commands (`Cmd.ml:213-215`). **It is not a block comment** — this
is the most dangerous false friend for a Twelf user, whose `%{ … %}` comments a
region out. In STELF the region *runs*.

```
%scope nat %{
  %term 0 nat %.
  %term S {_ nat} nat %.
%}
```

Only four commands take a block: `%scope`, `%eval`, `%data`, `%proof`. `%eval`
*requires* one; the other three also accept a single bare command.

```
%data nat %term zero nat        %; equivalent to a one-command block
```

Blocks nest arbitrarily and may be empty (`%data nat %{ %}`).

---

## 2. Lexical structure

There is no separate lexer. STELF is scannerless — the token rules are Angstrom
combinators in `Parser.ml`, and `%` is disambiguated by context. See
[`tokens.md`](tokens.md) for the complete tables.

### 2.1 Identifiers and the delimiter set `[changed]`

**Exactly ten bytes terminate an identifier** (`Parser.ml:62-65`):

```
space   tab   newline   (   )   {   }   [   ]   %
```

Everything else is an identifier character. This is the most consequential fact in
the language:

- `->` `<-` `+` `*` `:` `=` `,` `;` `?` `!` `#` `'` `"` `\` are ordinary names.
- Digits are ordinary name characters, so `0`, `123` and `3x` are identifiers.
- All bytes ≥ 0x80 pass through, so `ℕ`, `λ`, `⊢` are valid names.
- **`.` is not a delimiter.** `ns.name` lexes as the single identifier `"ns.name"`.
  There is no dotted-path syntax anywhere in STELF; namespaced references are
  written `%(ns name)` (§3.5). A parser that splits on `.` will diverge from the
  implementation.

Identifier **class** is decided by the first character (`Modern.ml:338-341`):

| First char | Class | Meaning |
|---|---|---|
| `A`–`Z` or `_` | uppercase | Metavariable — implicitly quantified, solved by unification |
| anything else | lowercase | Constant reference or bound variable |

So `X`, `Nat` and `_C1` are metavariables while `zero`, `λ`, `0` and `+` are not.
The class can be overridden lexically by `{{…}}` (§3.9).

The exact string `_` is in neither class: it is the omitted term (§3.3).

### 2.2 Escaping delimiters: `%%X` `[new]`

`%%` followed by **any single byte** contributes that byte literally to an
identifier (`Parser.ml:56-60`). This is how you write a name containing a
delimiter, or a name that would otherwise read as a keyword.

| Written | Identifier |
|---|---|
| `%%%` | `%` |
| `%%%term` | `%term` — the name, not the keyword |
| `%%(` | `(` |
| `%% ` | a single space |
| `%%!foo` | `!foo` |

A `%` run decomposes left to right by greedily pairing `%%`, so `%%%%` is `%`
followed by a bare `%` that *ends* the identifier. There is no other escape form:
no backslash escapes, no quoting, no `\n`.

The printer emits `%%` before every delimiter byte (`Lex.ml:27-38`), and renders
the empty name — which no source file can produce — as `%%_` (`Lex.ml:28`).

### 2.3 Keywords and the boundary rule

A keyword is `%` plus its body, and **must be followed by EOF or a delimiter**
(`Parser.ml:40-52`). Without this check, `keyword "term"` would match the `%term`
prefix of `%terminates` and the command dispatcher would commit to the wrong
branch.

A corollary: `%term.foo` is an *error*, not `%term` followed by `.foo`, because `.`
is not in the boundary set.

Keywords are recognised at parse time by string matching, not by a keyword table in
a lexer. [`tokens.md`](tokens.md) has the complete list across all layers.

### 2.4 Text literals: `%[ … %]` `[new]`

A text literal opens with `%` + *n* `[` and closes with `%` + *n* `]`, for any
*n* ≥ 1 (`Parser.ml:100-132`). The delimiters grow so that a payload containing the
closer can still be written.

```
%[hello world%]                  →  hello world
%[hello%world%]                  →  hello%world      (interior % is literal)
%[[hello%]world%]]               →  hello%]world     (n = 2)
%[[[a%]]]                        →  a                (n = 3)
```

Scanning rule: consume bytes until a `%`, then try to consume exactly *n* `]`. On
success the literal **ends immediately** — the scanner does not look further, so a
longer run of `]` closes at the *n*-th and leaves the rest in the stream. On
failure the `%` and the brackets actually consumed are appended to the payload
verbatim and scanning resumes.

- **There are no escapes inside a literal.** The payload is raw bytes.
- Reaching EOF first is an error: `%[hello` fails.
- `%[]` fails, because *n* = 1 makes `]` payload and the literal is never closed.

When *writing* a literal, choose the smallest *n* greater than the longest run of
`]` that immediately follows a `%` in the payload — this is what the printer does
(`Lex.ml:46-87`).

Text literals appear as term atoms, as the `%require` payload (§7.2), and as
ignorable prose between commands.

### 2.5 Comments `[changed]`

**There are no block comments.** A comment is `%` or `%;` followed immediately by
whitespace, running to end of line.

```
succ % a comment
zero
```

`%;` is an alternative introducer that reads better when a comment trails code on
the same line.

The rule differs slightly between the two contexts, deliberately:

| Context | Introducers | `%` + newline? |
|---|---|---|
| Inner — inside a term, anywhere whitespace is legal (`Parser.ml:17-30`) | `% ` `%\t` `%\n` `%;` | yes, is a comment |
| Outer — between commands (`Cmd.ml:32-58`) | `% ` `%\t`, or a run of **two or more** `%` | no, not a comment |

At outer level a run of ≥2 `%` starts a comment line, which is what makes wiki
metadata (`%%! title:`), banner rules (`%%%%%%`) and `%%`-commented-out code all
work. The `%`+newline case is excluded there so an empty trailing comment cannot
swallow the following declaration (`Cmd.ml:47-53`).

Because the probe requires a whitespace byte immediately after, `%%` (escape), `%[`
(text) and `%name` (keyword) are never mistaken for comments.

### 2.6 What is *not* in the lexer

- **No numeric literals.** Digit runs are matched ad hoc in exactly two places:
  `%prec` levels (`Modern.ml:643-647`) and `%query` bounds (`Modern.ml:685-690`).
  Neither does a boundary check, so `10x` reads as `10` then `x`.
- **No layout sensitivity.** Newlines are ordinary whitespace; there is no offside
  rule.
- **Known gaps**, stated as gaps rather than design: `\r` is neither whitespace nor
  a delimiter, so a CRLF file embeds `\r` in identifiers; and there is no UTF-8
  awareness, so Unicode whitespace is an identifier character (`Parser.ml:66`).

---

## 3. Expressions

The expression grammar has **three syntactic slots**, not a tower of precedence
levels (`Pretty.ml:21-34`):

| Slot | Parser | Contains |
|---|---|---|
| **Expr** | `parse_expr` (`Modern.ml:428-466`) | head forms, else `atom* trail?` |
| **Atom** | `parse_expr1` (`Modern.ml:415-426`) | identifiers, `(…)`, text literals |
| **Trail** | `parse_expr_trail` (`Modern.ml:354-407`) | binders and arrows — rightmost position only |

Everything in the `atom*` run is disambiguated afterwards by an operator-precedence
pass (§5).

| Construct | Syntax | Slot | Tag |
|---|---|---|---|
| Application | juxtaposition | — | `[shared]` |
| Identifier | `zero`, `X` | atom | `[shared]` |
| Omitted term | `_` | atom | `[shared]` |
| Universe | `%type` | atom | `[changed]` |
| Qualified name | `%(ns c)`, `%val c`, `%abs c` | atom | `[changed]` |
| Text literal | `%[ … %]` | atom | `[new]` |
| Lambda | `[x A] M` | trail | `[changed]` |
| Pi | `{x A} B` | trail | `[changed]` |
| Implicit scoping | `{{X Y}} M` | trail | `[new]` |
| Arrow | `%pi A %-> B`, `%pi B %<- A` | trail | `[changed]` |
| Local scope | `%local ns M`, `%(ns (M))` | head / atom | `[new]` |
| Ascription | `%the A M` | head | `[new]` |

### 3.1 Application `[shared]`

Juxtaposition, as in Twelf. There is no application operator.

```
succ zero
succ (succ zero)
```

A trailing form is appended as the **last argument**, which is why this parses:

```
f y z [x nat] x y z
```

### 3.2 The universe `%type` `[changed]`

Twelf's `type` is spelled `%type` so the bare identifier `type` stays available as
an ordinary name (`Modern.ml:306-314`).

```
%type          %; the universe
type           %; an ordinary lowercase identifier
```

`%type` exists mainly so the printer has a token for `IntSyn.Uni Type` that parses
back to the same term. **No command accepts it in a type-correct position** —
`%sort` supplies the universe implicitly, so `%sort c %type` is a level clash, not
a longhand.

### 3.3 The omitted term `_` `[shared]`

A lone `_` is a fresh placeholder, solved by reconstruction independently at each
occurrence.

The test is made on the **whole identifier** (`Modern.ml:285-294, 343-349`), so
`_0` and `_C1` are ordinary uppercase-class metavariables, not `_` followed by
something else. This matters because `Names.decLUName` generates names of exactly
that shape, so they arrive whenever printed output is read back in.

### 3.4 `%val` and `%abs` `[new]`

```
%val NAME              %val ( P₁ … Pₙ NAME )
%abs NAME              %abs ( P₁ … Pₙ NAME )
```

Both produce a *qualified reference*. In the parenthesised form the **last**
element is the name and everything before it is the namespace path, outermost
first (`Modern.ml:280-303`).

They differ in how an **unqualified** name resolves (`Cst.ml:17-24`):

- **`%val NAME`** is **shadow-aware**: it resolves to whichever binding is
  currently on top — an open `%scope`'s label if one shadows the name, else the
  toplevel one. Bare `NAME` and `%(NAME)` behave identically.
- **`%abs NAME`** is **toplevel-first**: it bypasses `%scope` shadowing and prefers
  the group's own toplevel declaration, falling back to `%val`'s behaviour only if
  there is none.

`%abs` exists because a `%scope` may install a case label that shadows a real
toplevel constant of the same name (§7.1). Qualified forms are identical for both,
since qualified lookup already ignores shadowing.

```
%sort pi1 atom %.
%term pi1 %pi atom %-> atom %.     %; toplevel primitive

%scope wf-noassm %term pi1 … %.    %; case label, shadows bare pi1 for this session

%abs pi1                           %; still the toplevel primitive
%val pi1                           %; the scope's case label
%abs ( wf-noassm pi1 )             %; the scope's case label — qualified, same as %val
```

`%val` is also the **universal escape hatch for a name that cannot be written
bare** (`Pretty.ml:88-94`): it opts a symbol out of operator status (§5), out of the
uppercase/lowercase classification (§2.1), and is the only spelling that can carry
a namespace.

```
%val +          %; the constant +, as a plain atom, even though + is infix
```

### 3.5 Qualified names `%(…)` `[changed]`

`%( P₁ … Pₙ NAME )` is shorthand for `%val ( P₁ … Pₙ NAME )` (`Modern.ml:317-334`).

```
%(nat 0)        %; the constant 0 declared inside scope nat
%(a b c)        %; c, in namespace a.b
```

Two details that bite:

- **No space is allowed between `%` and `(`.** This is matched as the raw string
  `"%("`, not through the keyword machinery. `%val (` *does* allow whitespace.
- **A qualified name is unconditionally an atom** (`Modern.ml:155-161`). It never
  consults the fixity table, so a namespaced operator can never be written — or
  printed — infix. That is a deliberate trade-off: explicit qualification opts out
  of operator status, and no spelling recovers it.

### 3.6 Local scopes `%(ns (M))` and `%local` `[new]`

Both open a scope for the extent of one expression, rewriting the names in `M` that
`ns` happens to provide and leaving everything else — bound variables in particular
— alone.

```
%(nat (S X))          %; S resolves in scope nat; X stays a metavariable
%local nat (ap F X)
```

> **The inner parentheses in `%(ns (M))` are mandatory.** Dropping them turns the
> node into `%(ns M)`, a *qualified name*, which demands that `ns` actually have a
> member `M`. `Local` only rewrites what it can (`Pretty.ml:135-140`).

`%local` is a head form: one namespace identifier, then a full expression, greedy to
the end.

### 3.7 Lambda and Pi `[changed]`

```
[decl] body            %; lambda   — Twelf [x:A] M
{decl} body            %; Pi       — Twelf {x:A} B
```

The colon is gone (§4). Both are trailing forms and may appear only in the
rightmost position of an expression, so an inner one needs parentheses.

```
f [x nat] x
f {x nat} x
f [p {_ nat} nat] z
```

### 3.8 Arrows `[changed]`

```
%pi A %-> B %-> C      ≡  A → (B → C)
%pi C %<- B %<- A      ≡  A → (B → C)
```

`%if`, `%do`, `%pi` and `%fn` are **exact synonyms** for the leading keyword
(`Modern.ml:373`); the printer always emits `%pi` (`Pretty.ml:196`). They read
differently in different roles — `%if` for a clause premise, `%pi` for a type — but
the parser does not distinguish them.

- `%->` is right-associative; the **last** element is the body.
- `%<-` reverses it: the **first** element is the body, matching Twelf's `A <- B`.
- **A leading keyword is required.** Bare `A %-> B` does not parse.
- **`%->` and `%<-` cannot be mixed in one chain.** The chain is built with a single
  separator, so `%pi A %-> B %<- C` parses `%pi A %-> B` and then fails on the
  leftover input.

Every element of a chain is a full expression that stops only at the next
separator, so an arrow in a non-final position would swallow the rest of the chain
— parenthesise it (`Pretty.ml:200-203`):

```
%pi (%pi A %-> B) %-> C
```

Arrows elaborate to a dedicated non-dependent `Arrow` node rather than an
anonymous-binder `Pi`, so the codomain is reconstructed without the domain in scope
(`Modern.ml:385-388`). Routing through `Pi` would over-scope the head's omitted
metavariables and derail coverage checking.

### 3.9 Explicit implicits `{{X Y}}` `[new]`

```
{{X Y}} X Y
{{X Y}} X {{Z}} Y Z
```

`{{…}}` scopes a list of names into the **uppercase class** for the body
(`Modern.ml:365-368, 45-51`), so they are treated as implicitly quantified
metavariables even when spelled lowercase. It produces no node of its own — it is
purely a lexical-classification device — and it nests.

> `{{` must be written glued. `{ {` lexes as a Pi binder whose declaration starts
> with `{`, and fails.

### 3.10 Type ascription `%the` `[new]`

```
%the TYPE TERM
```

**Type first.** `%the nat zero` ascribes `nat` to `zero`.

The type slot is an **atom**, so a compound type needs parentheses
(`Modern.ml:430-438`):

```
%the nat zero
%the (a b) x
%the a b c           %; = %the a (b c) — NOT (%the a b) c
```

The term slot is a full expression, greedy to the end. `%the` is a head form only:
there is no trailing form, so anything narrower than a full expression position
needs parentheses (`Pretty.ml:174-176`).

### 3.11 Terms with no surface syntax

The CST has constructors the parser never produces: `ExistVar`, `FreeVar`,
`BackArrow`, `Foreign`, `Internal`, `MacroParam` (`LENS.ml:126-150`). They exist for
the printer and for internal use, and `Internal` is deliberately unparseable. Do not
look for syntax for them.

---

## 4. Declarations (binders)

A declaration binds one or more names to a type. It appears in binders (`[…]`,
`{…}`), in `%term`, in `%sort` arguments, in `%block` items and in `%mode`.

```
decl ::= "(" arg+ ")" expr?        -- several names sharing one type
       | arg expr?                 -- one name
arg  ::= identifier                -- "_" means anonymous
```

`[changed]` from Twelf on three counts (`Modern.ml:494-517`):

**1. The colon is always elided.** `X : T` becomes `X T`.

```
{x nat} nat            %; Twelf: {x:nat} nat
```

**2. Several names may share a type**, by parenthesising them:

```
[(x y) nat] x          ≡  [x nat] [y nat] x
%term (true false) bool
```

> **Trap.** The parentheses are not optional. `[x y z t]` is **one** binder `x` of
> type `(y z t)` — not three binders. The bare-name branch takes exactly one
> argument and parses everything after it as the type, so this misparses silently.

**3. The type is optional**, yielding an inferred type:

```
[x] x
{x} x
(x y)
```

An omitted type is anchored on the binder's own source location, so
reconstruction's "ambiguous type" error underlines the binder rather than pointing
nowhere (`Modern.ml:498-502`).

`_` as the argument makes the binder anonymous. Because the test is on the whole
identifier, `{_0 nat}` binds the *name* `_0`; only a lone `_` is anonymous.

---

## 5. Fixity and precedence

### 5.1 Declaring fixity: `%prec` `[changed]`

Twelf's `%infix`, `%prefix` and `%postfix` are replaced by a single command:

```
%prec FIXITY LEVEL NAMES
```

```
%prec %right 3 @ %.
%prec %right 2 -> %.
%prec %middle 1 : %.
%prec %left 8 (++ --) %.
```

| Keyword | Fixity |
|---|---|
| `%left` | infix, left-associative |
| `%right` | infix, right-associative |
| `%middle` | infix, non-associative |
| `%none` | infix, non-associative — **identical to `%middle`** (`Modern.ml:112-113`) |
| `%prefix` | prefix |
| `%postfix` | postfix |

There is no `%nonfix`; an undeclared name is simply not an operator.

`LEVEL` is a run of decimal digits (`Modern.ml:643-647`), and **higher levels bind
more tightly**. The meaningful range is **0–9999**. Note the modern parser does
**not** range-check, unlike the legacy Twelf front end (`ParseFixity.ml:35-42`) — a
level above 9999 misbehaves rather than being rejected.

`%prec` registers the fixity as a **parse-time side effect** (`Cmd.ml:587`), so an
operator is usable in the same file immediately after its declaration.

> Two sharp edges. The parse-time table is keyed on the **unqualified** name, so
> `%prec %right 3 @` inside a `%scope` makes `@` infix everywhere, not just in that
> scope. And because it fires during parsing, it also fires on speculative branches
> that later backtrack.

### 5.2 The precedence ladder

| Level | Strength | Where |
|---|---|---|
| Atom | — | tightest |
| **Juxtaposition** | **10000**, left-associative | `Modern.ml:125-130` |
| `%prec` operators | 0–9999 | as declared |
| Trailing forms — binders, arrows | — | loosest, greedy to the end |

Application always binds tighter than any declarable operator, so `f x + g y` groups
as `(f x) + (g y)`.

### 5.3 Resolution

The `atom*` run is collected flat and then resolved by a shift/reduce
operator-precedence machine (`Modern.ml:176-278`) — the same design Twelf uses.
Ambiguity is a **hard error**, not a silent choice:

- infix following infix at equal precedence with mismatched associativity, which
  includes any two `%middle`/`%none` operators of the same level in a row
- infix following prefix at equal precedence
- postfix following prefix or infix at equal precedence
- consecutive infix operators, a leading infix, a leading postfix, or an incomplete
  infix or prefix expression

### 5.4 Bypassing fixity

Wrap the name in `%val` (§3.4). Because a qualified reference is always an atom,
this passes an operator as an ordinary argument:

```
%val +
%(term @) F X          %; @ is infix, but qualification makes it an atom
```

---

## 6. Commands

Every command begins with a `%`-keyword. The parser tries 39 alternatives in a fixed
order (`Cmd.ml:217-690`); the order matters where one keyword is a prefix of
another. The separator `%.` is itself one of those 39 (`Cmd.ml`'s first arm,
`Cst.Stop`) — which is why the count is 39 and not 38.

> The one-line summaries the REPL prints for `%help` live in
> [`src/Fronts/Pal/Help.ml`](../../src/Fronts/Pal/Help.ml), grouped by the same
> categories as the subsections below. A command added to the parser must be added
> to both; nothing checks that automatically, since `Cmd.ml` exposes no keyword
> list to compare against.

### 6.1 Declaring constants

| Command | Syntax | Effect | Tag | Twelf |
|---|---|---|---|---|
| `%sort` | `%sort NAMES DECL*` | Declare a type family | `[changed]` | `a : type.` |
| `%term` | `%term DECL` | Declare a term constant | `[changed]` | `c : A.` |
| `%def` / `%define` | `%def NAME TYPE? BODY` | Definition | `[changed]` | `c : A = M.` |
| `%inline` | `%inline NAME TERM` | Transparent definition | `[changed]` | `%abbrev c = M.` |
| `%block` | `%block NAME ITEM*` | Context block | `[changed]` | `%block b : some […] block {…}.` |
| `%union` | `%union NAME ( NAMES )` | Block union | `[changed]` | `%block b = b1 \| b2.` |
| `%symbol` | `%symbol ALIAS EXISTING` | Name alias | `[new]` | — |
| `%decl` | `%decl TERM` | Print a name's declaration | `[new]` | — |

**`%sort`** takes a name list — parenthesised for mutual families — and a sequence
of argument declarations. Each named argument `{x T}` becomes a dependent binder;
each anonymous one (`{_ T}` or a bare `T`) becomes a non-dependent arrow; the
universe terminating the kind is supplied implicitly.

```
%sort nat %.
%sort prop {_ nat} {_ nat} %.
%sort eq {t tp} {x term t} {y term t} %.
%sort (even odd) %.                       %; mutual
```

**`%term`** takes a single declaration, so several constants of the same type share
a line:

```
%term zero nat %.
%term succ {_ nat} nat %.
%term (true false) bool %.
```

**`%def`** reads the name (`_` allowed), then an *atom* as the optional type, then
the body:

```
%def not ({_ prop} prop) ([a] imp a false) %.
```

**`%inline`** is a definition installed transparently — always unfolded
(`Impl.ml:645-650`).

**`%block`** items use bare brackets, and the bracket shape carries the meaning
Twelf spells with the `some`/`block` keywords (`Modern.ml:711-722`):

| Item | Role |
|---|---|
| `[x T]` | *some* — a per-world variable, instantiated like a lambda binder |
| `{x T}` | block body — a hypothesis, like a Pi binder |

```
%block test [x nat] { y bool } %.
```

> [`LENS.ml:356-359`](../../src/Common/Cst/LENS.ml) documents these two backwards.
> The parser is authoritative.

### 6.2 Derived commands `[new]`

Three shorthands expand entirely in the parser; nothing downstream knows about them
(`Cmd.ml:352-469`).

**`%data NAME DECL* BODY`** → `%sort NAME DECL*` then `%scope NAME BODY`. A sort and
the constructors inhabiting it are one unit, so this writes the name once instead of
twice.

```
%data nat %{
  %term zero nat %.
  %term succ {_ nat} nat %.
%}
```

`NAME` must be a single identifier — `%scope` takes exactly one name, so mutual
sorts still need the long form.

**`%prop NAME FULL_MODE`** → `%sort` + `%mode`. A judgement's sort and its mode are
two views of the same information; this writes the argument list once instead of
three times.

```
%prop add {%in X nat} {%in Y nat} {%out Z nat} %.
%prop true %.                                    %; nullary is legal
```

Only the braced mode form is accepted here; the short positional form is not.

**`%proof (WORLD)? NAME FULL_MODE BODY`** → `%sort` + `%scope` + `%mode` +
`%worlds` + `%total`, in that order.

```
%proof (blk) total {%in X nat} {%out Z nat} %{ … %}
```

`WORLD` is optional and **must be parenthesised** — that is what keeps it
unambiguous against `NAME`. The `%scope` deliberately precedes the `%mode`: mode
checking runs retroactively over the whole family when the `%mode` is installed, so
it is clauses declared *after* it that would escape checking, not before.

### 6.3 Modes, worlds and totality `[shared]`

| Command | Syntax |
|---|---|
| `%mode` | `%mode {%in x A} … NAME args` or `%mode NAME %in %in %out` |
| `%worlds` | `%worlds ( NAMES ) ATOM+` |
| `%total` | `%total ORDER ATOM+` |
| `%terminates` | `%terminates ORDER ATOM+` |
| `%covers` | `%covers MODE_DEC` |
| `%reduces` | `%reduces REL ATOM+` |
| `%freeze` | `%freeze NAMES` |
| `%thaw` | `%thaw NAMES` `[new]` |
| `%deterministic` | `%deterministic NAMES` |
| `%unique` | `%unique NAME` `[new]` |

**Mode keywords are `%`-sigil words, not `+`/`-`/`*` sigils** `[changed]`:

| STELF | Alias | Twelf |
|---|---|---|
| `%in` | `%forall` | `+` |
| `%out` | `%exists` | `-` |
| `%out1` | — | `-1` |
| `%star` | — | `*` |

The braced and short forms may be mixed:

```
%mode {%in x nat} {%in y nat} {%out z nat} add x y z %.
%mode add %in %in %out %.
%mode {%in x nat} {%in y nat} add x y %out %.
```

**Termination orders** reuse the brackets a third way (`Cmd.ml:64-85`):

| Form | Meaning |
|---|---|
| `N` or `( N₁ N₂ )` | argument position(s) |
| `[ o … ]` | simultaneous |
| `{ o … }` | lexicographic |

Orders nest, and the empty order `{}` is legal — the corpus idiom for a
non-recursive totality proof.

```
%total N (add N _ _) %.
%total (N1 N2) (add N1 _ _) (mul N2 _ _) %.
%terminates {A [B C] F} (max A (max B C)) %.
```

**`%reduces`** takes a bare relation token — `<`, `<=`, `>`, `>=` or `=` — which is
*not* `%`-prefixed. `>` and `>=` are handled by swapping arguments; Twelf has only
`<` and `<=`.

```
%reduces < X Y add X Y zero %.
```

**`%worlds`** requires the parenthesised block list, which may be empty. Twelf's `|`
separator is gone.

```
%worlds () (add _ _ _) %.
%worlds (blk) (add N _ _) %.
```

### 6.4 Queries `[changed]`

| Command | Syntax |
|---|---|
| `%query` | `%query BOUND BOUND BOUND EXPR` |
| `%querytabled` | same shape |
| `%?` | `%? EXPR` `[new]` |
| `%solve` | `%solve EXPR` |

`%query` takes **three** bounds where Twelf takes two; `_` means unbounded. There is
no `X : A` result binding, and `%solve` likewise takes no name.

```
%query _ _ 1 add zero zero zero %.
%? add zero zero zero %.
```

`%?` is a STELF-only shorthand for an unbounded query, intended for the REPL.

### 6.5 Modules and files

Detailed in §7.

| Command | Syntax | Effect |
|---|---|---|
| `%scope` | `%scope NAME %{ COMMAND* %}` or `%scope NAME COMMAND` | Group declarations under a name; reopens an existing structure of that name (§7.1) |
| `%open` | `%open NAME`, `%open ( PREFIX NAME )`, `%open %require ARG` | Promote a structure's members to bare visibility (§7.3) |
| `%require` | `%require %[ path %]`, `%require ( a b c )`, `%require name` | Load a file; idempotent, and circular requires terminate (§7.2) |
| `%eval` | `%eval %{ COMMAND* %}` | Run a command list as one unit; the block is mandatory (§7.5) |
| `%use` | `%use …` | Module instantiation — parses, then fails (§6.7) |

### 6.6 REPL and meta commands

| Command | Syntax | Effect |
|---|---|---|
| `%help` | `%help` or `%help TOPIC` | Categorised list of every command; with `TOPIC`, one command or one category |
| `%version` | `%version` | Print the version |
| `%get` | `%get KEY` | Read back a key stored by `%set` (§6.7) |
| `%set` | `%set KEY VALUE` | Store a key; readable by `%get` only (§6.7) |
| `%quit` | `%quit` | Leave the REPL (Ctrl-D also works) |

Two things about `%help` follow from the grammar rather than from choice:

- **It still needs the separator.** The REPL submits a line only when it ends in
  `%.` (`Repl.ml:27-38`), so it is `%help %.`, not `%help`. Typing the latter just
  gives you the continuation prompt.
- **`TOPIC` is written bare.** The topic is parsed with `Modern.parse_var`
  (`Cmd.ml:605-612`), i.e. `ident1`, whose character class excludes `%`. So it is
  `%help sort %.`, not `%help %sort %.`. A topic may also name a category —
  `constants`, `derived`, `modes`, `queries`, `files`, `fixity`, `annotations`,
  `meta`, `separator`.

`%version` reports whatever the executable set, so `%version`, `stelf version` and
`stelf --version` always agree. The value comes from `dune-build-info`, which
`bin/main.ml` reads and assigns to `Impl`'s `version` option — the only place it
is set, and the only part of the tree depending on that library. Under a plain
`dune build` this resolves to `dune-project`'s `(version …)`; if artifact
substitution has not run, it falls back to `dev`.

Two consequences worth knowing:

- A library consumer of `pal` that never sets `M.version` sees `unknown`. That is
  deliberate — a library cannot know the version, since substitution rewrites a
  placeholder in the *linked executable*.
- `src/Frontend/Version.ml`'s `Stelf 1.7.1` string is the *Twelf* revision this
  port was taken from. It no longer reaches `%version`; it still serves the legacy
  Twelf-compatible frontend, where the number means something.

### 6.7 Commands that parse but do nothing

Flagged so they are not mistaken for working features:

| Command | Status |
|---|---|
| `%use` | Raises "module instantiation not yet implemented" (`Impl.ml:877-879`) |
| `%name` | No-op (`Impl.ml:703`); takes one identifier, unlike Twelf's `%name a X y.` |
| `%prose` | No-op (`Impl.ml:704`) — a highlighting hint |
| `%thaw` | Gated on `Global.unsafe`, which **nothing in this frontend sets** — the only assignment in the tree is the legacy server's `set unsafe` (`Server_.ml:174`), so `%thaw` always fails here |
| `%get` / `%set` | Read and write `Impl.Options`, a bare hashtable that nothing outside `%get` reads. A scratchpad, not a settings interface — no key changes any behaviour |
| `%symbol` | Installs a *name* alias only. It cannot alias keywords: the keyword-alias table is read but never written (`Modern.ml:30`) |

Each of these carries a matching `status` field on its entry in
[`Help.ml`](../../src/Fronts/Pal/Help.ml), so `%help` flags them too rather than
presenting them as working features.

> `Impl.ml` also handles a `Cst.Macro_` command with "Macros not yet implemented
> in this frontend", but the Modern parser has no `%macro` alternative, so that
> arm is unreachable from source text. It is deliberately absent from `Help.ml`
> for that reason — it is not an omission to fix.

---

## 7. Scopes, opening and files

### 7.1 `%scope` `[new]`

```
%scope NAME %{ COMMAND* %}
%scope NAME COMMAND
```

`%scope` groups declarations into a named structure. Semantically
(`Impl.ml:831-876`):

**Reopen-or-create.** If a structure of that name already exists in the current
namespace it is *reopened* and further declarations accumulate into it. This is what
lets you write one `%scope NAME` per clause:

```
%scope add %{ %term z {X nat} add zero X X %} %.
%scope add %{ %term s … %} %.
```

**Sessions.** While a scope is open, its members are also visible **bare**, without
qualification. The session closes as soon as the next top-level command is not a
`%scope` of the same name (`Impl.ml:458-474`) — a scope-declared name must not stay
shadowed forever. After that, members are reached by one of:

```
%(nat 0)               %; qualified reference          (§3.5)
%local nat (S X)       %; open for one expression      (§3.6)
%open nat              %; promote permanently          (§7.3)
```

**Shadow tolerance.** Inside a scope body an installation may reuse a label already
bound outside (`Impl.ml:151-171`), so a case named `pi1` can coexist with a toplevel
`pi1`. `%abs` (§3.4) is how you reach past such a shadow.

### 7.2 `%require` `[new]`

```
%require %[ some/path %]
%require ( a b c )
%require name
```

All three spellings produce a path: the text form is trimmed and split on `/`, the
identifier forms are joined with `/`. The `%[ … %]` spelling dominates the corpus
because it reads as a path rather than a name.

Resolution (`Loader.ml:31-78`):

1. The path's last segment is the stem; the **extension is not written**, so
   `%require %[ core %]` finds `core.lf`.
2. Each directory on the current load path is searched for a file whose basename
   without extension matches, excluding `.cfg` and `.toml`.
3. Files are deduplicated by canonical path, so repeated requires are idempotent and
   **circular requires terminate**.

A `%require` inside a `%scope` still loads into the *group* namespace, not the
scope's.

### 7.3 `%open` and `%open %require`

```
%open NAME
%open ( PREFIX NAME )
%open %require ARG
```

`%open` promotes a structure's members to bare visibility. At the top level the
effect is permanent; *inside* a `%scope` body the promoted names are retracted with
the rest of the body (`Impl.ml:810-820`).

`%open %require ARG` is the combined form. The two halves read the argument
differently — `%require` joins it into a *file path*, `%open` splits it into a
*structure path* — so they coincide only for a single-segment name, which is the
intended use (`Cmd.ml:534-538`).

The `%` sigil is what disambiguates: a scope literally named `require` is still
opened by the bare `%open require`.

### 7.4 There is no `%alias` command

`alias` is a **`stelf.toml` dependency field**, not syntax. It renames the namespace
a dependency is imported under (`Format.ml:5,59`; `Loader.ml:211-233`).

### 7.5 `%eval`

```
%eval %{ COMMAND* %}
```

Runs a command list as a single unit. The block is mandatory here.

---

## 8. Project files

A `stelf.toml` describes one or more groups:

```toml
#:schema ./stelf.schema.json

[[group]]
name = "demo"
main = "src/main.lf"
src = ["src"]
dependencies = []
```

| Key | Required | Notes |
|---|---|---|
| `name` | yes | Group name; also the namespace it is sealed into |
| `main` | yes | Entry-point file |
| `src` | — | Also spelled `dirs`, `srcs`, `dir`. Search path for `%require` |
| `dependencies` | — | Also spelled `deps` |

**There is no glob-based source discovery.** `src` is only the search path; the
actual file graph is `main` plus the `%require` edges reachable from it
(`Loader.ml:198-298`). A file that nothing requires is never compiled.

Dependencies are `local` (with an optional `alias`), `installed`, or `external`;
only `local` is currently loaded.

---

## 9. Migrating from Twelf

### Changed spellings

| Twelf | STELF |
|---|---|
| `a : type.` | `%sort a %.` |
| `c : A.` | `%term c A %.` |
| `c : A = M.` | `%def c A M %.` |
| `%abbrev c = M.` | `%inline c M %.` |
| `{x:A} B` | `{x A} B` |
| `[x:A] M` | `[x A] M` |
| `A -> B` | `%pi A %-> B` |
| `B <- A` | `%pi B %<- A` |
| `type` | `%type` |
| `+` / `-` / `-1` / `*` modes | `%in` / `%out` / `%out1` / `%star` |
| `%infix left 9 f.` | `%prec %left 9 f %.` |
| `%block b : some [x:T] block {y:U}.` | `%block b [x T] {y U} %.` |
| `%block b = b1 \| b2.` | `%union b (b1 b2) %.` |
| `%worlds (b1 \| b2) (f _ _).` | `%worlds (b1 b2) (f _ _) %.` |
| `s.c` (module path) | `%(s c)` |
| `.` terminator | `%.` |
| `%{ … }%` block comment | `% …` line comment |

### New in STELF

`%the` · `%local` · `%(ns (M))` · `{{X Y}}` · `%[ … %]` · `%%X` escapes · `%scope` ·
`%data` / `%prop` / `%proof` · `%?` · `%thaw` · `%unique` · `%symbol` · `%decl` ·
literate-by-default files · optional binder types · multi-name binders

### Absent from STELF

`%theorem` · `%prove` · `%establish` · `%assert` · `%clause` · `%tabled` ·
`%trustme` · `%subord` · `%sig` / `%struct` / `%include` · `%{ … }%` block comments

Several of these have CST constructors but no parser entry, so they report an
unrecognised command rather than a helpful "not supported" error.

---

## 10. Notes for implementors

### 10.1 Surface order vs CST order

Two constructs store their arguments in a different order than they are written.
Both swaps **type-check when written backwards**, because the two slots have the
same OCaml type — so they are worth checking against this table rather than
against intuition.

| Construct | Surface order | CST / view order | Built at |
|---|---|---|---|
| `%the` | `%the TYPE TERM` | `HasType (loc, term, type)` | `Modern.ml:430-438` |
| `%def` | `%def NAME TYPE BODY` | `Define (loc, name, body, type)` | `Modern.ml:660-676` |

Everything else stores its arguments in surface order.

### 10.2 Known defects

Documented here because they are traps, not because they are intended.

| Where | Problem |
|---|---|
| `LENS.ml:356-359` | `Any`/`All` block-item bracket shapes documented backwards |
| `Cst.ml:83` | Debug printer emits `%the TERM TYPE`, reversing the surface order |
| `Cmd.ml:257` | Comment refers to a `%mode`/`%module` collision; `%module` no longer exists |
| `Modern.ml:30` | `given_symbols` is read but never written — `%symbol` cannot alias keywords |
| `Modern.ml:409-413`, `Parser.ml:32` | `parse_expr_app` and `Parser.blank` are dead code |
| `Parser.ml:66` | `\r` is neither whitespace nor a delimiter; no UTF-8 awareness |
| `Modern.ml:643-647` | `%prec` accepts out-of-range levels the legacy parser rejects |
| `stelf.schema.json` | Says `action` where the TOML reader expects `post` |
