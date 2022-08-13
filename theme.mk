style.min.css : style.css dependencies-prebuild
	@scripts/pretty-echo.sh "Minifying" "CSS"
	@scripts/css.sh

ARTIFACTS += style.min.css

theme-build : style.min.css
