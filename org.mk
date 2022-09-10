ORG_IN := $(shell find site/ -name "*.org")
ORG_OUT := $(ORG_IN:.org=.html)

org-build : ${ORG_OUT}

soupault-build : org-build

ARTIFACTS += ${ORG_OUT} .emacs.d/cache

site/index.html : site/haskell.org site/miscellaneous.org site/meta.org site/coq.org

%.html : %.org org.mk
	@pretty-echo.sh  Exporting "$*.org"
	@capture.sh "$@" ${EMACS} --eval "(cleopatra:export-org \"$<\")"
