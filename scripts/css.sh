#!/bin/bash
minify="$(npm bin)/minify"
normalize="$(npm root)/normalize.css/normalize.css"
style="style.css"

# minify add a newline character at the end of its input
# we remove it using `head'
echo "
@charset \"UTF-8\";
$(cat ${normalize})
$(cat ${style})
" | ${minify} --css | head -c -1 > style.min.css
