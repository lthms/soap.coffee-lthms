IMAGES = $(wildcard img/*.png)
COMPRESSED_IMAGES = $(foreach img, ${IMAGES}, site/${img})
HIGHLIGHT_THEME = base16/unikitty-light
OCAML ?= ocaml-system

.PHONY: default
default: gen

.PHONY: gen-deps
gen-deps: build-ocaml-gen-deps build-node-deps

.PHONY: server-deps
server-deps: build-ocaml-server-deps

.PHONY: build-deps
build-deps: gen-deps server-deps build-ocaml-dev-deps

.PHONY: build-node-deps
build-node-deps: package-lock.json

dependencies.opam dev-dependencies.opam server.opam: dune-project _opam/.init
	dune build $@

.PHONY: build-ocaml-server-deps
build-ocaml-server-deps: _opam/.init server.opam
	@opam pin server . --no-action --yes
	@opam install server --deps-only --yes

.PHONY: build-ocaml-dev-deps
build-ocaml-dev-deps: _opam/.init dev-dependencies.opam
	@opam pin dev-dependencies . --no-action --yes
	@opam install dev-dependencies --deps-only --yes

.PHONY: build-ocaml-gen-deps
build-ocaml-gen-deps: _opam/.init dependencies.opam
	@opam pin dependencies . --no-action --yes
	@opam install dependencies --deps-only --yes

_opam/.init:
	@opam switch create . --no-install --packages ${OCAML},dune --yes || true
	@touch $@

package-lock.json: package.json
	@npm install

style.min.css: scripts/css.sh style.css package-lock.json
	@./scripts/css.sh

site/styles/highlight.css: package-lock.json .FORCE
	@cp $(shell npm root)/highlight.js/styles/${HIGHLIGHT_THEME}.css $@

site/img/%.png: img/%.png
	@pngcrush -q $^ $@

.PHONY: gen
gen: style.min.css site/styles/highlight.css ${COMPRESSED_IMAGES}
	@soupault

.PHONY: server
server:
	dune build server/main.exe --profile=release
	cp -f _build/default/server/main.exe soap.coffee

.PHONY: clean
clean:
	@rm -rf out/

.PHONY: serve
serve:
	@cd out/; python -m http.server 2> /dev/null

.PHONY: build-docker
build-docker:
	docker build \
		-f ./build.Dockerfile \
		--target soap.coffee \
		-t www/soap.coffee:latest \
		.

static: build-docker
	docker create --name soap-coffee-build www/soap.coffee:latest
	docker cp soap-coffee-build:/bin/soap.coffee .
	docker rm -f soap-coffee-build

.FORCE:
