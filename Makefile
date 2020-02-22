ROOT := $(shell pwd)
CLEODIR := site/posts/meta
EMACS := ROOT="${ROOT}" emacs
TANGLE := --batch --load="${ROOT}/scripts/tangle-org.el" 2>> build.log

GENFILES :=
CONTENTS :=
GENSASS :=

default: init-log build

init-log:
	@echo "==============[CLEOPATRA BUILD LOG]==============" \
	    > build.log

.PHONY: init-log default build

GENFILES += bootstrap.mk scripts/update-gitignore.sh
GENSASS += 

include bootstrap.mk

bootstrap.mk scripts/update-gitignore.sh  \
  &: ${CLEODIR}/Bootstrap.org
	@echo "  tangle  $<"
	@${EMACS} $< ${TANGLE}
