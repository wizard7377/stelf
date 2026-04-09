# STELF (Simple Theorems in the Edinburgh Logical Framework)

STELF is a port of the [Twelf](https://twelf.org) project, originally in [SML](https://smlfamily.github.io/), to [OCaml](https://ocaml.org/), as well as modernization efforts, such as improving the IDE interface, the build interface, the interlopability, among other efforts.

> [!NOTE]
> This is currently a work in progress, and is not yet fully functional

> [!WARNING]
> This project has two submodules, `twelf` and `basis`. The first of these need not be imported, but *the build will fail* without `basis`

Note that port in this case does mean a literal *port*, using the [Shibboleth](https://github.com/wizard7377/shibboleth) converter, we copied over the source litteraly, then fixed out kinks manually and used a [port](https://github.com/wizard7377/basis) of the SML Basis library.
Only after this is working (which has not yet happended) do we intend to make any subsantitive changes to the project itself.

## Goals of the Project

Of the goals, there are some more short and longer term ones that are listed here:

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

