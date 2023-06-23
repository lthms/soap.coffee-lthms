IMAGES = $(wildcard img/*.png)
COMPRESSED_IMAGES = $(foreach img, ${IMAGES}, site/${img})
HIGHLIGHT_THEME = base16/unikitty-light

.PHONY: default
default: build

.PHONY: build-deps
build-deps: build-ocaml-deps build-node-deps

.PHONY: build-node-deps
build-node-deps: package-lock.json

.PHONY: build-ocaml-deps
build-ocaml-deps: _opam/.init
	@opam pin dependencies . --no-action --yes
	@opam install dependencies --deps-only --yes

_opam/.init:
	@opam switch create . ocaml-system --yes --no-install --deps-only || true
	@touch $@

package-lock.json: package.json
	@npm install

style.min.css: style.css package-lock.json
	@./scripts/css.sh

site/styles/highlight.css: package-lock.json .FORCE
	@cp $(shell npm root)/highlight.js/styles/${HIGHLIGHT_THEME}.css $@

site/img/%.png: img/%.png
	@pngcrush -q $^ $@

.PHONY:build
build: style.min.css site/styles/highlight.css ${COMPRESSED_IMAGES}
	@soupault

.PHONY: clean
clean:
	@rm -rf out/

.FORCE:
