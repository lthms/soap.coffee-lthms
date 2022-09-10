style.min.css : style.css dependencies-prebuild
	@pretty-echo.sh "Minifying" "CSS"
	@css.sh

ARTIFACTS += style.min.css

theme-build : style.min.css
