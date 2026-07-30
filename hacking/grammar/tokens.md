# STELF Token Appendix

Flat tables for writing a lexer, a tree-sitter external scanner, or a syntax
highlighter. Prose and rationale live in [`stelf.md`](stelf.md); productions live
in [`stelf.ebnf`](stelf.ebnf).

Line numbers are as of the writing of this file; the surrounding construct is
named in each row so a drifted line is still findable.

---

## 1. The delimiter set

Exactly **ten bytes** terminate an identifier (`Parser.ml:62-65`, mirrored for the
printer at `Lex.ml:11-14`):

| Byte | Name |
|---|---|
| `0x20` | space |
| `0x09` | tab |
| `0x0A` | newline |
| `(` `)` | parens |
| `{` `}` | braces |
| `[` `]` | brackets |
| `%` | sigil |

**Everything else is an identifier character**, including:

```
. : ; , = < > + - * / ! ? # ^ ~ & | ' " \ @ $ ` 0-9   and all bytes >= 0x80
```

Consequences to encode:

- **`.` is not a delimiter.** `ns.name` is one identifier. Do not split on `.`.
- `->`, `<-`, `+`, `=` are ordinary names, not operators, until `%prec` says so.
- `ℕ`, `λ`, `⊢` are valid identifiers — no Unicode handling is needed, or present.
- **`\r` is neither whitespace nor a delimiter**, so a CRLF file embeds `\r` in
  identifiers (`Parser.ml:66` `TODO`). This is a bug, not a rule to reproduce.

---

## 2. Disambiguating `%`

`%` cannot be tokenised context-free. Its meaning depends on the following bytes
**and** on whether the scanner is between commands (outer) or inside a term
(inner).

| Lookahead | Outer context | Inner context |
|---|---|---|
| `%%` | comment to end of line | escape: `%%X` → literal `X` |
| `%[` | text literal, skipped as prose | text literal, a value |
| `%` + space or tab | comment to end of line | comment to end of line |
| `%` + newline | **not** a comment | comment to end of line |
| `%;` + whitespace | not handled | comment to end of line |
| `%` + ident | command keyword | term keyword |
| `%` + `(` | — | qualified name / local scope |
| `%` + anything else | parse error | parse error |

The outer scanner is `skip_outer` (`Cmd.ml:32-58`); the inner one is `whitespace`
(`Parser.ml:17-30`).

Two ordering rules inside `skip_outer`, both load-bearing:

1. `%[ … %]` is tried **first**, otherwise its `[` would be read as the second `%`
   of a `%%` comment.
2. A run of **two or more** `%` is consumed by one skip-to-newline, so an
   odd-length banner like `%%%%%` does not leave a stray `%` behind.

**A bare `%` is never a token.** It is always the start of one of the above.

---

## 3. Text literals need a counting scanner

```
opener  =  "%"  "["×n          n ≥ 1
closer  =  "%"  "]"×n          the same n
```

`Parser.ml:100-132`. The closer length is determined by the opener, so this is not
a regular language and needs an external scanner in tree-sitter.

- The scanner closes at the **first** `%` followed by n `]`, and does not look
  further — a longer run closes at the n-th and leaves the remainder.
- A `%` followed by fewer than n `]` is emitted into the payload verbatim.
- No escapes inside. EOF before the closer is an error.

| Input | Payload |
|---|---|
| `%[%]` | (empty) |
| `%[hello%world%]` | `hello%world` |
| `%[[hello%]world%]]` | `hello%]world` |
| `%[[[a%]]]` | `a` |
| `%[hello` | **error** — unterminated |
| `%[[hello%]` | **error** — n=2, only one `]` |
| `%[]` | **error** — n=1, `]` is payload |

Writer side (`Lex.ml:46-87`): choose the smallest n greater than the longest run of
`]` immediately following a `%` anywhere in the payload.

---

## 4. Identifier escapes

`%%` + any single byte → that byte, literally (`Parser.ml:56-60`).

| Source | Identifier |
|---|---|
| `%%%` | `%` |
| `%%%term` | `%term` |
| `%%(` | `(` |
| `%% ` | ` ` (one space) |
| `%%!foo` | `!foo` |
| `%%%%` | `%`, then a bare `%` **ends** the identifier |

A trailing bare `%%` at EOF fails: the escape requires a following byte.

The empty identifier has no source spelling; the printer emits `%%_`
(`Lex.ml:28`).

---

## 5. Keyword boundary rule

```
keyword  =  "%" body  followed-by ( EOF | delimiter )
```

`Parser.ml:40-52`. Without the boundary check, `keyword "term"` matches the
`%term` prefix of `%terminates` and the command dispatcher commits to the wrong
branch.

Corollary: since `.` is not a delimiter, **`%term.foo` is an error**, not `%term`
followed by `.foo`.

Keywords also consume trailing whitespace and comments.

---

## 6. Keywords by layer

### 6.1 Command layer — `Cmd.ml`

Listed in **parser order**, which is the order alternatives are tried.

| Keyword | Line | Notes |
|---|---|---|
| `%{` `%}` | 214, 215 | command block — **not** a comment |
| `%.` | 222 | separator, not a terminator |
| `%querytabled` | 229 | **must precede `%query`** |
| `%query` | 237 | three bounds |
| `%?` | 244 | unbounded query |
| `%unique` | 254 | |
| `%scope` | 262 | |
| `%mode` | 278 | |
| `%define` `%def` | 287 | both spellings |
| `%decl` | 294 | |
| `%inline` | 301 | |
| `%symbol` | 312 | |
| `%freeze` | 323 | |
| `%thaw` | 331 | needs the `unsafe` flag |
| `%sort` | 339 | |
| `%data` | 365 | derived |
| `%prop` | 399 | derived |
| `%proof` | 436 | derived |
| `%term` | 471 | tried before `%terminates` |
| `%block` | 478 | |
| `%union` | 489 | |
| `%worlds` | 500 | |
| `%deterministic` | 511 | |
| `%use` | 519 | parses, unimplemented |
| `%open` | 541 | |
| `%require` | 543, 566 | 543 is the `%open %require` form |
| `%eval` | 573 | |
| `%prec` | 580 | mutates the fixity table at parse time |
| `%solve` | 592 | |
| `%quit` | 598 | |
| `%help` | 605 | |
| `%get` | 615 | |
| `%set` | 622 | |
| `%version` | 632 | |
| `%total` | 639 | |
| `%terminates` | 650 | |
| `%covers` | 661 | |
| `%name` | 668 | no-op |
| `%prose` | 674 | no-op |
| `%reduces` | 681 | |

### 6.2 Term layer — `Modern.ml`

| Keyword | Line | Notes |
|---|---|---|
| `%type` | 313 | the universe; bare `type` is an ordinary name |
| `%val` | 315 | qualified reference, shadow-aware |
| `%abs` | 316 | qualified reference, toplevel-first |
| `%(` | 317 | **raw `string "%("`** — no space permitted after `%` |
| `%if` `%do` `%pi` `%fn` | 373 | exact synonyms; arrow-chain heads |
| `%->` | 376, 379 | right-associative; last element is the body |
| `%<-` | 394, 397 | first element is the body |
| `%the` | 431 | ascription, **type first** |
| `%local` | 440 | |

### 6.3 Mode layer — `Modern.ml`

| Keyword | Line | Twelf |
|---|---|---|
| `%out1` | 532 | `-1` |
| `%out` `%exists` | 535 | `-` |
| `%in` `%forall` | 539 | `+` |
| `%star` | 542 | `*` |

Tried in that order, so `%out1` is matched before `%out`.

### 6.4 Fixity layer — `Modern.ml`

| Keyword | Line | Fixity |
|---|---|---|
| `%left` | 726 | infix, left |
| `%right` | 728 | infix, right |
| `%prefix` | 730 | prefix |
| `%postfix` | 732 | postfix |
| `%middle` | 734 | infix, non-associative |
| `%none` | 736 | infix, non-associative — identical to `%middle` |

### 6.5 Keywords of dead sub-grammars

Reachable from no command. Do not highlight them as keywords.

| Keyword | Line | Belongs to |
|---|---|---|
| `%where` | 611 | `parse_sigexp` |
| `%the`, `%(` | 606, 482–485 | `parse_sigexp`, `parse_qualified` |

`parse_sigexp`, `parse_sigdef`, `parse_struct_dec`, `parse_inst` and
`parse_qualified` are exported from `MODERN.ml` but only reference each other; no
`cmd` alternative uses them.

---

## 7. Bare tokens — the unbounded ones

These are matched with `Parser.token` (`Parser.ml:33`), a **raw string match with
no boundary check**, then trailing whitespace.

| Token | Where |
|---|---|
| `(` `)` | grouping, id-lists, multi-name binders, qualified paths, world lists |
| `[` `]` | lambda, block `some` item, simultaneous order |
| `{` `}` | pi, block body item, lexicographic order, moded declaration |
| `{{` `}}` | implicit-variable scoping — matched as the two-byte string, not two `{` |
| `_` | `%query` bound (`Modern.ml:687`) |
| `<=` `>=` `<` `>` `=` | `%reduces` relation (`Modern.ml:703-707`), longest first |

> **Prefix hazard.** Because there is no boundary check, these bite into longer
> identifiers. `token "<="` matches the front of `<=>` and leaves `>` behind;
> `token "_"` matches the leading `_` of `_X` and leaves `X`.
>
> `Modern.parse_arg` (`Modern.ml:285-294`) documents having hit exactly this bug —
> `token "_"` turned `{_0 nat}` into an anonymous binder of type `0 nat`. Its fix
> is the pattern to copy: **match a whole identifier, then classify it.**

---

## 8. Ordering hazards

In dispatch order, the cases where one keyword prefixes another:

1. **`%querytabled` before `%query`** (`Cmd.ml:225`) — explicit comment.
2. **`%term` before `%terminates`** (`Parser.ml:36-39`) — the boundary check is
   what makes this safe; without it `%term` would match and commit.
3. **`%out1` before `%out`** (`Modern.ml:532-535`).
4. **`%define` and `%def`** are one alternative (`Cmd.ml:287`), tried longest first.
5. **`%open %require` before plain `%open`** (`Cmd.ml:541-547`) — the `%` sigil on
   `require` is what disambiguates, so a scope literally named `require` is still
   opened by bare `%open require`.
6. **`%[ … %]` before `%%`** inside `skip_outer` (`Cmd.ml:36-38`).
7. **`<=` / `>=` before `<` / `>`** (`Modern.ml:703-707`).

---

## 9. What is not a token class

- **No numeric literals.** Digits are identifier characters. Digit runs are matched
  ad hoc in two places only: `%prec` levels (`Modern.ml:643-647`) and `%query`
  bounds (`Modern.ml:685-690`). Model these as contextual, not as a `number` token.
- **No string quoting.** The only string-like construct is `%[ … %]`.
- **No operator token class.** Operator-ness is a *dynamic* property set by
  `%prec` at parse time, not a lexical one.
- **No layout sensitivity.** Newline is ordinary whitespace.
- **No block comments.**

---

## 10. Suggested highlighting classes

| Class | Matches |
|---|---|
| `keyword.command` | `%`-keywords from §6.1 |
| `keyword.operator` | `%->`, `%<-`, `%if`, `%do`, `%pi`, `%fn`, `%the`, `%local` |
| `keyword.modifier` | mode (§6.3) and fixity (§6.4) keywords |
| `constant.builtin` | `%type` |
| `variable` | identifiers whose first byte is `A`–`Z` or `_` (metavariables) |
| `variable.builtin` | the exact identifier `_` |
| `function` / `constant` | all other identifiers — the two are indistinguishable lexically |
| `string` | `%[ … %]` |
| `comment` | `% …`, `%; …`, and `%%`-runs at outer level |
| `constant.character.escape` | `%%X` inside an identifier |
| `punctuation.bracket` | `( ) [ ] { } {{ }} %{ %}` |
| `punctuation.delimiter` | `%.` |

Notes for a highlighter:

- **Constants and functions cannot be told apart lexically.** Both are lowercase
  identifiers; the distinction is semantic (arity, declared kind). Either use one
  class for both, or resolve it from `%sort` / `%term` declarations.
- **Do not highlight namespaces by splitting on `.`.** Namespace structure appears
  only inside `%( … )`, `%val ( … )` and `%abs ( … )`, as space-separated
  identifiers.
- `%{ … %}` should be highlighted as a **block, not a comment** — the most likely
  mistake to make when adapting a Twelf grammar.

---

## 11. Round-trip obligation

[`src/Pretty/Lex.ml`](../../src/Pretty/Lex.ml) is the printer-side inverse of this
lexer and its header declares the sync obligation explicitly. It implements:

| Function | Line | Inverse of |
|---|---|---|
| `is_delimiter` | 11-14 | the delimiter set (§1) |
| `escape_ident` | 27-38 | `%%X` escapes (§4) |
| `max_closer_run` / `quote_text` | 49-87 | text-literal delimiter counting (§3) |
| `is_upper` | 41-44 | identifier class (§1) |

Any lexer written from this document should be validated against `Lex.ml`'s output:
a divergence means one of the two is wrong.
