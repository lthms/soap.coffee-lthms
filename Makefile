ROOT := $(shell pwd)
CLEODIR := site/posts/meta
EMACS := ROOT="${ROOT}" emacs

GENFILES := scripts/tangle-org.el bootstrap.mk

default: build

include bootstrap.mk

Makefile bootstrap.mk scripts/tangle-org.el \
  &: ${CLEODIR}/Bootstrap.org
	@echo "  tangle  $<"
	@${EMACS} $< --batch \
	   --eval "(require 'org)" \
	   --eval "(cd (getenv \"ROOT\"))" \
	   --eval "(setq org-src-preserve-indentation t)" \
           --eval "(org-babel-do-load-languages 'org-babel-load-languages'((shell . t)))" \
           --eval "(setq org-confirm-babel-evaluate nil)" \
	   --eval "(org-babel-tangle)"
