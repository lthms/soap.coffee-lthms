ROOT := $(shell pwd)
CLEODIR := site/posts/meta/
GENFILES := scripts/tangle-org.el bootstrap.mk

include bootstrap.mk

bootstrap.mk scripts/tangle-org.el &: site/posts/meta/Bootstrap.org
	@echo "  tangle  $<"
	@ROOT="${ROOT}" emacs $< --batch \
	                  --eval "(require 'org)" \
	                  --eval "(setq org-src-preserve-indentation t)" \
	                  --eval "(org-babel-tangle)"

.PHONY: clean build force
