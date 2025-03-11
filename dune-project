(lang dune 3.8)
(using coq 0.8)

(name coq-pil)

(source
 (github hferee/rocq-pil))

(authors "Hugo Férée"
         "Sam van Gool"
         "Pablo Iglesias Vasquez")

(maintainers "Hugo Férée")

(license CecILL)

(homepage https://hferee.github.io/UIML)
(documentation https://hferee.github.io/UIML/toc.html)


(package
 (name coq-pil)
 (synopsis "Propositional quantifiers for modal logics formalised")
 (description "")
 (allow_empty)
 (depends ocaml dune coq-stdpp angstrom exenum)
 (tags
  (coq "intuitionistic logic" "proof theory" "propositional quantifiers" "extraction")))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/dune-files.html#dune-project
