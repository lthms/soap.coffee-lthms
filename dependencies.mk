OCAML_VERSION := 4.12.0
OCAML := ocaml-base-compiler.${OCAML_VERSION}

_opam/init :
	@scripts/pretty-echo.sh "Creating" "a local Opam switch"
	@opam switch create . ${OCAML} --repos default,coq-released || true
	@scripts/pretty-echo.sh "Installing" "OCaml dependencies"
	@opam install dune.2.9.0 coq-coqffi.1.0.0~beta7 coq-simple-io.1.5.0 soupault.4.0.1 coq.8.13.2 coq-compcert.3.8 -y
	@touch $@

CONFIGURE += _opam

package-lock.json : package.json
	@scripts/pretty-echo.sh "Installing" "frontend dependencies"
	@npm install

CONFIGURE += package-lock.json node_modules

dependencies-prebuild : _opam/init package-lock.json
