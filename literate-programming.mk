literate-programming-prebuild : site/posts/CoqffiEcho.org
	@scripts/pretty-echo.sh "Tangling" "literate programming project"
	@capture.sh tangling-lp ${EMACS} --eval "(cleopatra:export-lp)"

ARTIFACTS += lp/ site/posts/deps.svg

COQFFI_ARCHIVE := site/files/coqffi-tutorial.tar.gz

${COQFFI_ARCHIVE} : literate-programming-prebuild _opam/init
	@scripts/pretty-echo.sh "Building" "coqffi tutorial"
	@cd lp/coqffi-tutorial; dune build --display quiet
	@scripts/pretty-echo.sh "Archiving" "coqffi tutorial"
	@rm -f ${COQFFI_ARCHIVE}
	@capture.sh coqffi-tutorial tar --exclude="_build" -C lp/ -czvf ${COQFFI_ARCHIVE} coqffi-tutorial

literate-programming-build : ${COQFFI_ARCHIVE}
soupault-build : literate-programming-build

ARTIFACTS += ${COQFFI_ARCHIVE}
