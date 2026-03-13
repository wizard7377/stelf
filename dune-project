(lang dune 3.20)

(name twelf)

(generate_opam_files true)

(source
 (github username/reponame))

(authors "Author Name <author@example.com>")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)
;(pin
; (url "git+https://github.com/wizard7377/basis.git")
; (package (name basis)))
(package
 (allow_empty)
 (name twelf)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends
   ocaml 
   basis
   lwt
 )
 (tags
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
