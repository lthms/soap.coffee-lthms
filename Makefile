SASS       := $(shell find site/ -name "*.sass")
ORG_POSTS  := $(shell find site/ -name "*.org")
COQ_POSTS  := $(shell find site/ -name "*.v")
INPUTS     := $(ORG_POSTS:.org=.html) $(COQ_POSTS:.v=.html) $(SASS:.sass=.css)

COQCARGS   := -async-proofs-cache force

build: ${INPUTS}
	@soupault
	@scripts/update-gitignore.sh ${INPUTS}

clean:
	rm -f ${INPUTS}
	rm -rf build

force: clean build

%.html: %.v
	@echo "export $*.v"
	@coqc ${COQCARGS} $*.v
	@coqdoc --no-index --charset utf8 --short --body-only -d site/posts/ \
	        --coqlib "https://coq.inria.fr/distrib/current/stdlib/" \
	        $*.v
	@sed -i -e 's/href="$(shell basename $*.html)\#/href="\#/g' $*.html
	@rm -f site/posts/coqdoc.css

%.html: %.org
	@echo "export $*.org"
	@emacs $< --batch --eval "(setq org-html-htmlize-output-type nil)" --eval "(org-html-export-to-html nil nil nil t)" --kill

%.css: %.sass
	@echo "compile $*.sass"
	@sassc --style=compressed --sass $< $@

.PHONY: clean build force
