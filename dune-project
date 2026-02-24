(lang dune 3.20)

(name rampart)

(generate_opam_files true)

(source
 (github alastairpatrick/rampart))

(authors "Alastair Patrick")

(maintainers "Maintainer Name <maintainer@example.com>")

(license LICENSE)

(documentation https://url/to/documentation)

(using menhir 3.0)

(package
 (name rampart)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml)
 (tags
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
