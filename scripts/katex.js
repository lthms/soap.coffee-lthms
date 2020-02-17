/* Render inline maths using KaTeX */
var katex = require("katex");
var fs = require("fs");
var input = fs.readFileSync(0);

var html = katex.renderToString(String.raw`${input}`, {
    throwOnError: false
});

console.log(html)
