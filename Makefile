ROOT := $(shell pwd)
CLEODIR := site/cleopatra

GENFILES :=
GENAUX :=
CONTENTS :=
GENSASS :=

EMACSBIN := emacs
EMACS := ROOT="${ROOT}" ${EMACSBIN}
TANGLE := --batch --load="${ROOT}/scripts/tangle-org.el" 2>> build.log

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
