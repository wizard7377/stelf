# STELF Project

![STELF Logo](./logo.png)

> "It is only prudent never to place confidence in that by which we have even once been deceived."
>
> René Descartes

The STELF (System for Totality in the Edinburgh Logical Framework), is minimal system designed for creating understandable and completely trustworthy proofs.
STELF is based off the [Twelf Theorem Prover](https://twelf.org).

The best resource for learning about STELF is the [STELF website](https://standardocaml.github.io/).

Some other quick links:

1. [STELF website](https://standardocaml.github.io/)
2. [STELF GitHub](https://github.com/standardocaml)
3. [Twelf website](https://twelf.org)
4. [Twelf GitHub](https://github.com/standardml/twelf)

## Installation

> [!WARNING]
> I have not as of yet tested that this is reproducible, please create an issue if you have a problem

These are the quick installation instructions

### Prerequisites

Most of STELF's requisites are installed automatically.
However, this setup process has two dependencies.
Fortunately, they are quite easily available.

1. `make`: GNU Make is fine, other versions are almost certainly also fine but this has only been tested with GNU Make (if it is called something like `make` it is probably fine)
2. `opam`: The OCaml package manager, which is used to install OCaml and project dependencies.
   See [opam's installation instructions](https://opam.ocaml.org/doc/Install.html) for your platform if you don't have `opam` installed.
   Note that if you use the process outlined here you do **not** need to install `ocaml`, `dune`, or anything else, or setup a switch; the [Makefile](./Makefile) does this all automatically

### Sources

The source code for STELF can be obtained from this repository, if you want to install the stable version, the command would be:

```sh
git clone --recurse-submodules https://github.com/standardocaml/stelf.git
cd stelf
```

If, on the other hand, you want the most up to date `dev` version, instead run

```sh
git clone --recurse-submodules --branch=dev https://github.com/standardocaml/stelf.git
cd stelf
```

### Building

To install, build, document, test, or check the project, use the appropriate `make` target.
Those being:

- `make install` to install the project
- `make build` to build the project (create `./stelf`)
- `make doc` to generate documentation (in `_build/default/doc`)
- `make test` to run tests
- `make check` to check that the project can compile

### Editor Support

Currently, the officially supported editor extensions are for [Zed](https://github.com/standardocaml/stelf-zed) and [Neovim](https://github.com/standardocaml/stelf.nvim).
We describe here how to install the Neovim extension, due to the simplicity thereof.

1. Have [nvim-treesitter](https://github.com/nvim-treesitter/nvim-treesitter)
2. Install the extension `standardocaml/stelf.nvim`, which *must not be lazy loaded*
3. Run `:TSUpdate` and `:TSInstall stelf`, then reload
4. Load up a `.lf`, `.elf`, `.stelf`, or `.slf` file and enjoy syntax highlighting!

All together, if you use LazyVim you should have something like this

```lua
return {
  {
    'standardocaml/stelf.nvim', 
    dependencies = 'nvim-treesitter/nvim-treesitter', 
    lazy = false,
    build = {':TSUpdate', ':TSInstall stelf'},
  }
}
```

> [!NOTE]
> Other editor extensions are appreciated. Further, fixes and additions upon the existing extensions is greatly appreciated (currently, they just provide syntax highlighting using Tree-Sitter).
> Also, a more general editor server protocol (perhaps LSP) would be quite useful.

## Building

### Testing

For end-user testing, just run `make test`.
Developers should use `dune test`.

## Improvements from Twelf

Twelf itself is a powerful tool for reasoning about metatheorems, but it had several limitations and shortcomings

### Ecosystem

Twelf's is arguably one of its weakest points.
Twelf, a Standard ML program, requires an SML compiler, which is a task in itself.
In addition, the Twelf Emacs mode, while not a core part of the project, is not very modernized and is not on `MELPA`, which makes it another setup

STELF is written in OCaml, a modern language in the ML family with a very large ecosystem (that is also the basis of the Rocq project).
Its build is easy and user friendly.

### Composability

Twelf had a large *large* problem with composability.

Firstly, Twelf's module system was never fully implemented (in Twelf, it serves as the basis for the scope system here).
This means that if you wanted to make sure names didn't collide, you had to be sure that they were distinct.
This means names had to either be at least one of (usually both)

- Very, *very* long
- Not descriptive

In addition, Twelf did not have a clear way to import other files or to have libraries.
The configuration system is a list of files to be loaded, in order.
STELF uses a `stelf.toml` file (which is compliant TOML), which fixes all these problems.
In addition, you get the much needed scope feature, allowing names like `%(nat zero)` to be written without aggressively adding dashes

### Candy

The original Twelf, compared to modern languages (including STELF) has a bit of a simple REPL

1. Input and output can't be distinguished in the Twelf REPL (STELF has `=>`, `debug` etc. for output, and `λ∏>` or `>` for input)
2. The Twelf REPL doesn't use color (STELF does))
3. The Twelf REPL doesn't have a command history (STELF does)

## Copyright

Copyright (C) 1997-2011, Frank Pfenning and Carsten Schuermann
Copyright (C) 2026, Asher Frost (Ethan Moy)
