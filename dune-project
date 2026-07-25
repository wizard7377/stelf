(lang dune 3.21)

(name stelf)

(version 1.0.0~alpha)

(generate_opam_files true)

(source
 (github standardocaml/stelf))

(authors "Asher Frost <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license BSD-2-Clause)

(documentation https://github.com/standardocaml/stelf/wiki)

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
  lwt
  containers
  base
  angstrom
  (alcotest :with-test)
  (alcotest-lwt :with-test)
  grace
  notty-community
  (odoc :with-doc)
  (sherlodoc :with-doc)
  (ocamlformat :dev)
  (ocaml-lsp-server :dev)
  (user-setup :dev)
  (merlin :dev)
  ; (js_of_ocaml :with-doc)
  ; (js_of_ocaml-compiler :with-doc) 
  ; (js_of_ocaml-ppx :with-doc) 
  ; (js_of_ocaml-lwt :with-doc)
  sexplib
  ppx_deriving
  lambda-term
  fmt
  bos
  cmdliner 
  logs
  otoml)
 (tags
  ("logic" "language" stelf)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
