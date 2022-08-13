serve :
	@cleopatra echo Spwaning "HTTP server"
	@cd out && python -m http.server

update :
	@scripts/pretty-echo "Updating" "OCaml dependencies"
	@opam update
	@opam upgrade -y
