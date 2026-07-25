# Copilot Instructions for stelf

## Quick build / test / lint commands
- dune build                # build (many modules may fail; expected)
- dune build @check         # fast type-check only
- dune runtest              # run all tests
- dune exec bin/main.exe    # run Pal frontend (REPL/CLI)
- dune fmt                  # format (ocamlformat 0.28.1)
- make build/test/docs      # Makefile targets: `make build`, `make test`, `make docs`
- make check                # runs `dune build @check` via Makefile

Running a single test
- Two Alcotest suites live under test/:
  - test/Pal/PalTest.ml  → dune exec test/Pal/PalTest.exe
  - test/Parse/ParseTest.ml → dune exec test/Parse/ParseTest.exe -- test '<suite>' <n>
- For debugging a failing test: run its executable directly (dune exec ...), read output, then inspect the test file in test/*/Cases.ml.

Notes
- Do NOT use `dune utop` or `make repl` — utop preloads compiler-libs which conflicts with project modules (e.g., Lambda, Lexer, Parser).
- The `basis/` directory is a pinned submodule providing SML basis shims. Clone with submodules:
  git clone --recurse-submodules <repo>
  or: git submodule update --init

## High-level architecture (big picture)
- ~40 Dune libraries under src/, layered roughly:
  - Foundation: global, trail, table, stream, timing
  - Core LF: src/IntSyn (IntSyn, Whnf, Conv, Unify, Abstract)
  - Middle: names, paths, print, index, modes, subordinate, typecheck, modules
  - Analysis: terminate, thm, cover, meta, prover, tomega
  - Execution: compile, opsem, solvers
  - Frontend: src/frontend (Lexer, Parser, Recon*, Twelf_, Frontend_, Solve)
- Two frontend variants to know: `modern` (parser) and `pal` (combined frontend used by bin/main.exe).
- Many modules are wired by functor instantiation in *_.sml.ml files; top-level wiring is in src/frontend/frontend_.sml.ml.

## Key repository conventions (non-obvious)
- Two source styles:
  - Old-style (most src/*): three-part module pattern concatenated by Dune:
    - .sig.ml (signature), .fun.ml (functor implementation), .sml.ml (instantiation/wiring)
    - Check `sources.dune` files in subdirs for concatenation rules.
  - New-style (src/Common, src/Recon, src/Lang, src/frontend, src/Fronts): single-file modules and explicit interfaces.
- Naming:
  - SML structure → OCaml `module Foo`
  - SML signature → `module type FOO`
  - Functors → `module MakeFoo(...)` or `module Foo(...)`
  - Constructors colliding with OCaml keywords append `_` (ok_, abort_, Type_)
- Compatibility:
  - Old-style files `open Basis` and prefer Basis.* (Basis.Array, Basis.List) over OCaml stdlib.
  - Old-style libraries: `wrapped = false` and build flags include `-w -A -open Basis`.
  - New code should be `wrapped = true`.
- Formatting: ocamlformat 0.28.1 (default profile).
- Tests: test cases are in test/*/Cases.ml; Common.ml has helpers.
- Submodules: `basis/` and `twelf/` are submodules; ensure initialized when building.

## Where to look first when investigating
1. Re-run the failing test (dune exec path/to/Exe) and read its output.
2. Open the test Cases.ml and the code under test in src/ that the test imports.
3. Limit early file reads to ~3 files; then form a hypothesis before deeper searches.
4. Use `dune build @check` to perform a fast type-check.

## Other AI/assistant configs in repo
- CLAUDE.md (project guidance for Claude)
- .github/agents/ocaml-doc-converter.agent.md
- Keep these in sync when updating instructions.

Summary: updated instructions include exact Makefile/dune commands, single-test examples, submodule notes, and the three-file module convention.
