(lang dune 3.7)
(generate_opam_files true)
(authors "Thomas Letan <lthms@soap.coffee>")
(maintainers "Thomas Letan <lthms@soap.coffee>")
(homepage "https://soap.coffee/~lthms")
(bug_reports "mailto:~lthms/public-inbox@lists.sr.ht")

(package
  (allow_empty)
  (synopsis "OCaml dependencies for lthms’ website generation")
  (name dependencies)
  (depends soupault crunch dream sha camlzip))

(package
  (allow_empty)
  (synopsis "OCaml dependencies for lthms’ website server")
  (name server)
  (depends crunch dream sha camlzip))

(package
  (allow_empty)
  (synopsis "OCaml dependencies for hacking lthms’ website")
  (name dev-dependencies)
  (depends ocaml-lsp-server ocamlformat utop))

