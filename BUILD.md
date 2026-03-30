# Building STELF

This document describes how to set up dependencies and build STELF locally.

STELF is an in-progress OCaml port of Twelf. Some areas of the codebase are
still under active translation, so occasional compile failures in unfinished
subsystems can be expected.

## Prerequisites

- OCaml 5.0 or newer
- opam 2.1 or newer
- dune 3.20 or newer

Optional but useful:

- `ocamlformat` (for formatting)
- `odoc` (for docs)

## One-Time Setup

From the repository root:

```bash
opam switch create . ocaml-base-compiler.5.1.1
eval "$(opam env)"

# Pin local basis package used by this repository
opam pin add -y basis ./basis

# Install dependencies for stelf
opam install -y . --deps-only --with-test --with-doc
```

If you already have a switch for this repo, you can skip switch creation and
just run:

```bash
eval "$(opam env)"
opam pin add -y basis ./basis
opam install -y . --deps-only --with-test --with-doc
```

## Build Commands

### Standard Build

```bash
dune build
```

### Release Build

```bash
dune build --profile=release
```

### Check Profile Build

```bash
dune build --profile=check
```

## Run Tests

```bash
dune test
```

Or run the test alias explicitly:

```bash
dune build @runtest
```

## Format Code

```bash
dune fmt
```

## Build Documentation

```bash
dune build @doc
```

## Build Executable

The main executable is built via dune:

```bash
dune build bin/main.exe
```

After a successful build, the binary is available under `_build/default/bin/`.

## Using Makefile Targets

Common targets:

```bash
make build
make test
make fmt
make check
```

Note: the `install` target currently depends on `build-release`, which is not
defined in the current Makefile. Prefer dune commands directly for installation
flows until that target is updated.

## Troubleshooting

- If dune cannot find dependencies, ensure your opam switch is active:

	```bash
	eval "$(opam env)"
	```

- If `basis` resolves incorrectly, re-pin local basis and reinstall deps:

	```bash
	opam pin add -y basis ./basis
	opam install -y . --deps-only --with-test --with-doc
	```

- If build failures appear in partially ported modules, verify whether the
	failure is in actively translated code before treating it as a regression.
