ROOT := $(shell pwd)
CLEODIR := site/cleopatra

ARTIFACTS := build.log
CONFIGURE :=

EMACSBIN := emacs
EMACS := ROOT="${ROOT}" ${EMACSBIN}
TANGLE := --batch \
          --load="${ROOT}/scripts/tangle-org.el" \
          2>> build.log

define emacs-tangle =
echo "  tangle  $<"
${EMACS} $< ${TANGLE}
endef

default : postbuild ignore

init :
	@rm -f build.log

prebuild : init

build : prebuild

postbuild : build

.PHONY : init prebuild build postbuild ignore

include bootstrap.mk

prebuild : bootstrap-prebuild
build : bootstrap-build
postbuild : bootstrap-postbuild

bootstrap-prebuild : bootstrap.mk scripts/update-gitignore.sh
bootstrap-build : bootstrap-prebuild
bootstrap-postbuild : bootstrap-build

bootstrap.mk scripts/update-gitignore.sh &:\
   ${CLEODIR}/Bootstrap.org
	@$(emacs-tangle)

CONFIGURE += bootstrap.mk scripts/update-gitignore.sh

.PHONY : bootstrap-prebuild \
         bootstrap-build \
         bootstrap-postbuild
