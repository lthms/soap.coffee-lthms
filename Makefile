SASS := $(shell find site/ -name "*.sass")
INPUTS := $(SASS:.sass=.css)
MAKEFILES := bootstrap.mk
ROOT := $(shell pwd)
GEN_SCRIPTS := scripts/tangle-org.el
EMACSARGS := --batch --eval "(require 'org)" \
             --eval "(org-babel-do-load-languages 'org-babel-load-languages '((shell . t)))" \
             --eval "(org-babel-tangle)"

include ${MAKEFILES}

bootstrap.mk scripts/tangle-org.el &: site/posts/meta/Bootstrap.org
	@echo "  tangle  $<"
	@ROOT="${ROOT}" emacs $< ${EMACSARGS} 2>/dev/null

.PHONY: clean build force
