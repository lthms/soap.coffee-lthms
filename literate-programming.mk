literate-programming-prebuild : org-prebuild
	@scripts/pretty-echo.sh "Tangling" "literate programming project"
	@${EMACS} --eval "(cleopatra:export-lp)"

ARTIFACTS += lp/ site/posts/deps.svg

COQFFI_ARCHIVE := site/files/coqffi-tutorial.tar.gz

coqffi-tutorial-build : literate-programming-prebuild _opam/init
	@scripts/pretty-echo.sh "Building" "coqffi tutorial"
	@cd lp/coqffi-tutorial; dune build --display quiet
	@scripts/pretty-echo.sh "Archiving" "coqffi tutorial"
	@rm -f ${COQFFI_ARCHIVE}
	@tar --exclude="_build" -C lp/ -czvf ${COQFFI_ARCHIVE} coqffi-tutorial

site/posts/CoqffiEcho.html : coqffi-tutorial-build
literate-programming-build : coqffi-tutorial-build

ARTIFACTS += ${COQFFI_ARCHIVE}
