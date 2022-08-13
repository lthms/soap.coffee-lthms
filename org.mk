ORG_IN := $(shell find site/ -name "*.org")
ORG_OUT := $(ORG_IN:.org=.html)

org-prebuild : .emacs
org-build : ${ORG_OUT}

soupault-build : org-build

ARTIFACTS += ${ORG_OUT} .emacs.d/cache
CONFIGURE += .emacs

.emacs : scripts/packages.el
	@scripts/pretty-echo.sh echo Initiating  "Emacs configuration"
	@${EMACS}
	@touch .emacs

site/index.org : site/haskell.org site/miscellaneous.org site/meta.org site/coq.org

%.html : %.org scripts/packages.el scripts/export-org.el .emacs org.mk
	@scripts/pretty-echo.sh  Exporting "$*.org"
	@${EMACS} $< --load="$(shell pwd)/scripts/export-org.el"
