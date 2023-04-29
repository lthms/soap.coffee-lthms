OCAML_VERSION := 4.14.1
OCAML := ocaml-base-compiler.${OCAML_VERSION}

_opam/init :
	@pretty-echo.sh "Creating" "a local Opam switch"
	@opam switch create . ${OCAML} --repos default,coq-released || true
	@pretty-echo.sh "Installing" "OCaml dependencies"
	@opam install dune.3.7.1 coq-coqffi.1.0.0~beta8 coq-simple-io.1.5.0 soupault.4.5.0 coq.8.13.2 coq-compcert.3.8 coq-serapi mustache -y
	@touch $@

CONFIGURE += _opam

package-lock.json : package.json
	@pretty-echo.sh "Installing" "frontend dependencies"
	@npm install

CONFIGURE += package-lock.json node_modules

dependencies-prebuild : _opam/init package-lock.json
