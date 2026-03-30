# STELF (Simple Theorems in the Edinburgh Logical Framework)

STELF is a port of the [Twelf](https://twelf.org) project, originally in [SML](https://smlfamily.github.io/), to [OCaml](https://ocaml.org/), as well as modernization efforts, such as improving the IDE interface, the build interface, the interlopability, among other efforts.

> [!NOTE]
> This is currently a work in progress, and is not yet fully functional

Note that port in this case does mean a literal *port*, using the [Shibboleth](https://github.com/wizard7377/shibboleth) converter, we copied over the source litteraly, then fixed out kinks manually and used a [port](https://github.com/wizard7377/basis) of the SML Basis library.
Only after this is working (which has not yet happended) do we intend to make any subsantitive changes to the project itself.

## Goals of the Project

Of the goals, there are some more short and longer term ones that are listed here:

### Short term goals

- [X] Get the Twelf/Stelf server as is working correctly
- [X] Get the testing infrastructure working, also add expected output and expected failure tests
- [ ] Change references of Twelf to Stelf
  
### Medium Term Goals

- [ ] Port the wiki to a easier to use format (likely either `mld`, `typ`, `tex`, or some combination)
- [ ] Port the documentation to odoc style
- [ ] Make the server output nicer (add REPL, using `lambda-term`)
- [ ] Reimplement the lexer and parser to be easier to understand and more efficient, preferably using `menhir`

### Long Term Goals


- [ ] Split up the concrete syntax and abstract syntax into completely different libraries (ie, one that deals with the internals and another that deals with parsing)
- [ ] Make better IDE support (Perhaps using LSP?)
- [ ] Remove the `=` and `:` special syntax 
- [ ] Add support for generics

## Links

- [Contributing](CONTRIBUTING.md)
- [Style Guide](STYLE.md)
- [License](LICENSE)
- [Building](BUILD.md)

## Credits

While I actually was the one to convert the project, a translator is nothing without a work to translate.
As such, credit is in large part due to the original writers of the Twelf project; per the [README](twelf/README.md)

### Original Twelf Source Code

Copyright (C) 1997-2011, Frank Pfenning and Carsten Schuermann

Authors:

    Frank Pfenning
    Carsten Schuermann

With contributions by:

    Brigitte Pientka
    Roberto Virga
    Kevin Watkins
    Jason Reed

### STELF Proper

Copyright (C) 2026, Asher Frost

[^1]: A number of ideas stolen from a similar project, [ELPI](https://github.com/LPCIC/elpi/blob/master/ELPI.md)

