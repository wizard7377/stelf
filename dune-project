(lang dune 3.20)

(name twelf)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)
(pin
 (url "file://basis")
 (package (name basis)))
(package
 (allow_empty)
 (name twelf)
 (synopsis "A short synopsis")
 (description "A longer description")
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
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
