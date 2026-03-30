# Style Guide

This document defines naming, structure, and documentation conventions for OCaml code in this repository.

## Naming

### Capitalization

Use `snake_case` for names that start with a lowercase letter. This includes values, functions, and types.

Use `CamelCase` for capitalized names that are not module types.

For related names that differ only by a prefix or suffix, `_` may be used to separate parts when it improves readability. Each part should still be in `CamelCase`. This is most common for functors, which should generally be named `Make_` followed by a descriptive name.

Use screaming `SNAKE_CASE` for module types.

### Module Names

If there is a module `Mod`, its module type should be `MOD`.

If a functor produces modules of type `MOD`, it should generally be named `Make_Mod`.

### Trailing Underscores

Trailing underscores in names are usually artifacts of SML-to-OCaml conversion. Remove them when possible, unless they are required to avoid keyword collisions or preserve behavior.

## Simplification Rules

### Boolean Algebra

Prefer direct boolean expressions over redundant branching.

- Do not write `if cond then ... else false`; write `cond && ...`
- Do not write `if cond then true else ...`; write `cond || ...`
- Do not write `match x with true -> ... | false -> ...`; write `if x then ... else ...`
- Do not write `if x then false else true`; write `not x`

### Brevity

- For one-clause functions, prefer `fun` over `function`
- Avoid unnecessary nested `let`; use `let ... and ...` when bindings are independent
- Do not use `let rec` unless recursion is needed

### General

New functions should be curried by default.

## Scope and Modules

Avoid global `open` declarations. Prefer either:

- module-qualified names, or
- small, local `open` scopes.

The idiom `open! struct ... end in ...` is usually a conversion artifact and should be avoided when possible. In particular, avoid aliases like `let f = f`.

### Libraries and DRY

For new code, prefer OCaml Stdlib and `containers` over adding new `basis` usage when practical.

Use existing combinators (`map`, `fold`, etc.) instead of hand-written boilerplate.

### Organizing Modules

Prefer one module per file.

For module `M.ml`, add a corresponding `M_intf.ml` containing its module type. Include the module type in `M.ml` and use it to constrain the public signature.

### Functor Parameters

Prefer separate functor parameters over bundling many modules into one anonymous `sig` block.

Instead of:

```ocaml
module Make_Mod (M : sig
    module X : A
    module Y : B
    module Z : C
end) : MOD = struct
    ...
end
```

Prefer:

```ocaml
module Make_Mod (X : A) (Y : B) (Z : C) : MOD = struct
    ...
end
```

### `mli` Files

Each library (`compile`, `lambda`, etc.) should provide at least one `mli` file describing the public interface for the library.

## Formatting and Nesting

### `begin ... end` vs `( ... )` (Inside Values)

Use `begin ... end` in these cases:

1. Grouping expressions sequenced with `;`
2. Delimiting long `match` expressions where boundaries are otherwise unclear
3. Clarifying branch boundaries inside `match`, `if`, and similar constructs

In most other value-level cases, use `( ... )`.

## Documentation

Use correct [odoc](https://ocaml.github.io/odoc/) comments for all public code.

Documentation should explain what something is and how it is intended to be used. Public interfaces should be understandable without reading implementation details.

Document at least the following public items:

- types and constructors
- values and functions
- modules and module types
- exceptions

Private items should be documented when it improves maintainability.

### Tags

Keep `@author` tags accurate.

For public members, include:

- `@param` for each parameter
- `@return` for return values
- `@raise` for exceptions and triggering conditions
- `@see` for related symbols

### File-Level Docs

Each file should start with a header comment and a one-sentence synopsis.

### Position of Documentation

Place documentation immediately adjacent to the item it documents.

For declarations, place doc comments immediately before the declaration. Keep blank lines minimal so formatting remains stable under `ocamlformat`.

### Markup

Use odoc markup correctly:

1. `{_ ...}` for subscripts and `{^ ...}` for superscripts
2. `{e ...}` for emphasis
3. `{1 ...}`, `{2 ...}`, etc. for section headers
4. `{: ...}` for links
5. `{! ...}` for references
6. `[ ... ]` for inline code, `{[ ... ]}` for OCaml code blocks, and `{v ... v}` for generic verbatim blocks
7. `{m ...}` for inline math and `{math ...}` for math blocks (LaTeX/KaTeX syntax)
