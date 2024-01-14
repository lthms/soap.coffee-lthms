#!/bin/bash
normalize="$(npm root)/normalize.css/normalize.css"
github_colors="$(npm root)/markdown-it-github-alerts/styles/github-colors-light.css"
github_base="$(npm root)/markdown-it-github-alerts/styles/github-base.css"
style="style.css"

# minify add a newline character at the end of its input
# we remove it using `head'
echo "
@charset \"UTF-8\";
$(cat ${normalize})
$(cat ${github_colors})
$(cat ${github_base})
$(cat ${style})
" | npx minify --css > style.min.css
