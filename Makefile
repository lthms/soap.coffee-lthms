SASS       := $(shell find site/ -name "*.sass")
INPUTS     := $(SASS:.sass=.css)
MAKEFILES  := org.mk coq.mk

include ${MAKEFILES}

build: ${INPUTS} soupault.conf
	@echo "run soupault"
	@soupault
	@echo "update gitignore"
	@scripts/update-gitignore.sh ${INPUTS} ${MAKEFILES}

clean:
	@echo "remove generated makefiles"
	@rm -f ${MAKEFILES}
	@echo "remove generated files in site/"
	@rm -f ${INPUTS}
	@echo "remove build/ directory"
	@rm -rf build

force: clean build

soupault.conf: site/posts/meta/Soupault.org
	@echo "generate soupault.conf"
	@emacs $< --batch --eval "(org-babel-tangle)" --kill 2>/dev/null

org.mk coq.mk &: site/posts/meta/Contents.org
	@echo "generate org.mk, coq.mk"
	@emacs $< --batch --eval "(org-babel-tangle)" --kill 2>/dev/null

%.css: %.sass
	@echo "compile $*.sass"
	@sassc --style=compressed --sass $< $@

.PHONY: clean build force
