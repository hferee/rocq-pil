(lang dune 3.8)

(name rocq-pil)

(generate_opam_files true)

(source
 (github hferee/UIML))

(authors "Hugo Férée"
         "Sam van Gool"
         "Yago Iglesias Vasquez")

(maintainers "Hugo Férée")

(license CecILL)

(homepage https://hferee.github.io/)
(documentation https://hferee.github.io/UIML/toc.html)

(using coq 0.8)

(package
 (name rocq-pil)
 (synopsis "Propositional Intuitionistic Logic - Pitts Interpolation Library")
 (description "")
 (allow_empty)
 (depends ocaml dune coq-stdpp coq-equations)
 (tags
  (coq "intuitionistic logic" "proof theory" "propositional quantifiers" "extraction")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
