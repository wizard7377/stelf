(lang dune 3.20)

(name stelf)

(generate_opam_files true)

(source
 (github wizard7377/stelf))

(authors "Asher Frost <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)
(pin
 (url "file://basis")
 (package (name basis)))
(package
 (allow_empty)
 (name stelf)
 (synopsis "A port of Twelf to OCaml")
 (description "STELF (System for the Typed Edinburgh Logical Framework) is a port of Twelf to OCaml. It provides a framework for defining and reasoning about formal systems, such as programming languages and logics.")
 (depends
   (ocaml (>= 5.0.0)) 
   basis
   lwt
   containers 
   (alcotest :with-test)
  (odoc :with-doc)
  
   (logs (>= 3.0.0)) 
 )
 (tags
  ("logic" "language" stelf)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
