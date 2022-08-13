ARTIFACTS :=
CONFIGURE := .emacs.d

PROCS := $(wildcard *.mk)
PROCS_DEPS := $(foreach proc,$(PROCS:.mk=.deps),.${proc})

CMD ?= postbuild

EMACS := ROOT=$(shell pwd) emacs -Q --load="scripts/init.el" --load="scripts/packages.el" --batch

init : ${PROCS_DEPS}
	make ${CMD}

.%.deps : %.mk makefile
	@scripts/gen-deps.sh $< $@

-include ${PROCS_DEPS}

prebuild :
build : prebuild
postbuild : build

postbuild :
	@scripts/update-gitignore.sh $(sort ${CONFIGURE} ${ARTIFACTS} ${PROCS_DEPS})
	@rm -f $(wildcard .*.deps)

clean :
	@rm -rf ${ARTIFACTS}

cleanall : clean
	@rm -rf ${CONFIGURE}
