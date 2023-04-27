serve :
	@pretty-echo.sh "Spwaning" "HTTP server"
	@cd out && python -m http.server

update :
	@pretty-echo.sh "Updating" "OCaml dependencies"
	@opam update
	@opam upgrade -y
