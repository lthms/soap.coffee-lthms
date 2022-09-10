PATH := scripts/:${PATH}

ARTIFACTS := logs/*.stderr logs/*.stdout
CONFIGURE := .emacs.d

PROCS := $(wildcard *.mk)
PROCS_DEPS := $(foreach proc,$(PROCS:.mk=.deps),.${proc})

CMD ?= postbuild

EMACS_NAME=cleopatra

EMACS := emacsclient -s ${EMACS_NAME}

init : ${PROCS_DEPS} needs-emacs
	@make ${CMD}

needs-emacs :
	@pretty-echo.sh "Starting" "emacs daemon"
	@${EMACS} -s ${EMACS_NAME} --eval "(kill-emacs)" 2> /dev/null || true
	@ROOT=$(shell pwd) capture.sh "start-server" emacs --daemon=${EMACS_NAME} -Q --load="scripts/init.el"

.PHONY : needs-emacs

.%.deps : %.mk makefile
	@gen-deps.sh $< $@

-include ${PROCS_DEPS}

prebuild :
build : prebuild
postbuild : build

postbuild :
	@pretty-echo.sh "Updating" ".gitignore"
	@update-gitignore.sh $(sort ${CONFIGURE} ${ARTIFACTS} ${PROCS_DEPS})
	@pretty-echo.sh "Killing" "emacs daemon"
	@${EMACS} -s ${EMACS_NAME} --eval "(kill-emacs)"
	@rm -f $(wildcard .*.deps)

.PHONY: prebuild build postbuild

clean :
	@rm -rf ${ARTIFACTS}

cleanall : clean
	@rm -rf ${CONFIGURE}

.PHONY : clean cleanall
