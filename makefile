ARTIFACTS :=
CONFIGURE := .emacs.d

PROCS := $(wildcard *.mk)
PROCS_DEPS := $(foreach proc,$(PROCS:.mk=.deps),.${proc})

CMD ?= postbuild

EMACS_NAME=cleopatra

EMACS := emacsclient -s ${EMACS_NAME}

init : ${PROCS_DEPS} needs-emacs
	make ${CMD}

needs-emacs :
	@scripts/pretty-echo.sh "Starting" "emacs daemon"
	@${EMACS} -s ${EMACS_NAME} --eval "(kill-emacs)" || true
	@ROOT=$(shell pwd) emacs --daemon=${EMACS_NAME} -Q --load="scripts/init.el"

.PHONY : needs-emacs

.%.deps : %.mk makefile
	@scripts/gen-deps.sh $< $@

-include ${PROCS_DEPS}

prebuild :
build : prebuild
postbuild : build

postbuild :
	@scripts/pretty-echo.sh "Updating" ".gitignore"
	@scripts/update-gitignore.sh $(sort ${CONFIGURE} ${ARTIFACTS} ${PROCS_DEPS})
	@scripts/pretty-echo.sh "Killing" "emacs daemon"
	${EMACS} -s ${EMACS_NAME} --eval "(kill-emacs)"
	@rm -f $(wildcard .*.deps)

.PHONY: prebuild build postbuild

clean :
	@rm -rf ${ARTIFACTS}

cleanall : clean
	@rm -rf ${CONFIGURE}

.PHONY : clean cleanall
