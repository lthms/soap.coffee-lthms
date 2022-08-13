COQ_POSTS := $(shell find site/ -name "*.v")
COQ_HTML := $(COQ_POSTS:.v=.html)
COQ_ARTIFACTS := $(COQ_POSTS:.v=.vo) \
  $(COQ_POSTS:.v=.vok) \
  $(COQ_POSTS:.v=.vos) \
  $(COQ_POSTS:.v=.glob) \
  $(join $(dir ${COQ_POSTS}),$(addprefix ".",$(notdir $(COQ_POSTS:.v=.aux))))

coq-build : ${COQ_HTML}

soupault-build : coq-build

ARTIFACTS += ${COQ_ARTIFACTS} .lia.cache
ARTIFACTS += ${COQ_HTML}

COQLIB := "https://coq.inria.fr/distrib/current/stdlib/"
COQCARG := -async-proofs-cache force \
           -w -custom-entry-overriden
COQDOCARG := --no-index --charset utf8 --short \
             --body-only --coqlib "${COQLIB}" \
             --external "https://coq-community.org/coq-ext-lib/v0.11.2/" ExtLib \
             --external "https://compcert.org/doc/html" compcert \
             --external "https://lysxia.github.io/coq-simple-io" SimpleIO

%.html : %.v coq.mk _opam/init
	@scripts/pretty-echo.sh Exporting  "$*.v"
	@coqc ${COQCARG} $<
	@coqdoc ${COQDOCARG} -d $(shell dirname $<) $<
	@rm -f $(shell dirname $<)/coqdoc.css
