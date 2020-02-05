ORG_POSTS  := $(wildcard site/posts/*.org)
COQ_POSTS  := $(wildcard site/posts/*.v)
POSTS      := $(ORG_POSTS:.org=.html) $(COQ_POSTS:.v=.html)

COQCARGS   := -async-proofs-cache force

build: ${POSTS}
	@soupault
	@scripts/update-gitignore.sh ${POSTS}

clean:
	rm -f ${POSTS}
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

.PHONY: clean build force
