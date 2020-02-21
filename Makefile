ROOT := $(shell pwd)
CLEODIR := site/posts/meta
GENFILES := scripts/tangle-org.el bootstrap.mk
EMACS := ROOT="${ROOT}" emacs

default: build

include bootstrap.mk

Makefile bootstrap.mk scripts/tangle-org.el \
  &: ${CLEODIR}/Bootstrap.org
	@echo "  tangle  $<"
	@${EMACS} $< --batch \
	   --eval "(require 'org)" \
	   --eval "(setq org-src-preserve-indentation t)" \
	   --eval "(org-babel-tangle)" 2>/dev/null
