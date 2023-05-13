(lang dune 3.7)
(generate_opam_files true)
(authors "Thomas Letan <lthms@soap.coffee>")
(maintainers "Thomas Letan <lthms@soap.coffee>")
(homepage "https://soap.coffee/~lthms")
(bug_reports "mailto:~lthms/public-inbox@lists.sr.ht")

(package
  (allow_empty)
  (synopsis "OCaml dependencies for lthms’ website")
  (name dependencies)
  (depends soupault))

