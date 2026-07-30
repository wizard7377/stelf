(lang dune 3.21)

(name stelf)

(version 1.0.0~alpha2)

(generate_opam_files true)

; Required for test/STELF's (cram ...) stanza to run at all -- without this the
; suite is silently inert. Project-wide, but the only *.t paths dune scans here
; are test/STELF/{Nat,STLC,TSLF}.t; TEMPLATE/ is excluded as data_only there.
(cram enable)

(source
 (github standardocaml/stelf))

(authors "Asher Frost <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license BSD-2-Clause)

(documentation https://standardocaml.github.io/)

(pin
 (url "basis")
 (package
  (name basis)))

(package
 (allow_empty)
 (name stelf)
 (synopsis "A port of Twelf to OCaml")
 (description
  "STELF (System for the Typed Edinburgh Logical Framework) is a port of Twelf to OCaml. It provides a framework for defining and reasoning about formal systems, such as programming languages and logics.")
 (depends
  (ocaml
   (>= 5.0.0))
  (dune
   (>= 3.24))
  ; Used only by bin/, to stamp the executable's version -- see bin/main.ml.
  dune-build-info
  ; Lower bounds are the versions in dune.lock -- the set local builds actually
  ; resolve against, and so the only combination known to compile. CI cannot use
  ; dune.lock (it is gitignored) and resolves through opam instead, so without
  ; these the two can silently drift apart.
  lwt
  (containers
   (>= 3.18))
  base
  (angstrom
   (>= 0.16.1))
  (alcotest
   (and
    :with-test
    (>= 1.9.1)))
  (alcotest-lwt :with-test)
  grace
  (notty-community
   (>= 0.2.4))
  (odoc :with-doc)
  (sherlodoc :with-doc)
  (ocamlformat :dev)
  (ocaml-lsp-server :dev)
  (user-setup :dev)
  (merlin :dev)

  sexplib
  ppx_deriving
  (lambda-term
   (>= 3.4.0))
  (fmt
   (>= 0.11.0))
  (bos
   (>= 0.3.0))
  ; 1.3.0, not the locked 2.1.1: bin/main.ml uses Term.Syntax, Cmd.eval' and
  ; Cmd.Exit.info, all of which 1.3.0 already provides.
  (cmdliner
   (>= 1.3.0))
  (logs
   (>= 0.10.0))
  (otoml
   (>= 1.0.5)))
 (tags
  ("logic" "language" stelf)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
