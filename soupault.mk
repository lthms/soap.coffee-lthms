CONFIGURE += _opam rss.json
ARTIFACTS += out

soupault-prebuild : _opam/init

soupault-build : dependencies-prebuild style.min.css
	@pretty-echo.sh "Executing" "soupault"
	@soupault
