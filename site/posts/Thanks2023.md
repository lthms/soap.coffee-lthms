---
published: 2023-06-23
abstract: |
    In the past, I had a page called “Thanks!” dedicated to listing the free
    and open source software projects I was relying on to create this website.
    I do want to approach this exercise differently this time: instead of
    keeping one page up to date with the latest software stack I am using, I
    will publish a new article every now and then. This article is the first of
    this series.
tags:
  - meta
---

# The Free and Open Source Software Projects This Website is Built Upon in June 2023

In the past, I had a page called “Thanks!” dedicated to listing the free and
open source software projects I was relying on to create this website. Sadly,
this page was dropped during my latest overhaul, which is a shame because I do
think it is important to acknowledge these fantastic projects without which
this website would not exist.

That being said, I do want to approach this exercise differently this time.
Instead of keeping one page up to date with the latest software stack I am
using, I plan to publish a new article every now and then[^gratitude].

[^gratitude]: I really like the idea of keeping track of all the wonderful
    tools I was lucky enough to find out and use over the years.

## Authoring Contents

As mentioned in [my latest retrospective](/posts/May2023.html), I have
simplified how I write my contents. Nowadays, all my write-ups
are written in Markdown, and I use
[markdown-it](https://github.com/markdown-it/markdown-it) to parse them and
generate nice and fancy HTML documents.

In addition to the base parser that markdown-it is, I am relying on an
ever-growing collection of plugins:

- [markdown-it-footnote](https://www.npmjs.com/package/markdown-it-footnote)
- [markdown-it-figure](https://www.npmjs.com/package/markdown-it-figure)
- [markdown-it-highlightjs](https://www.npmjs.com/package/markdown-it-highlightjs)
- [markdown-it-meta](https://www.npmjs.com/package/markdown-it-meta)
- [markdown-it-custom-block](https://www.npmjs.com/package/markdown-it-custom-block)
- [markdown-it-mermaid](https://www.npmjs.com/package/markdown-it-mermaid)
- [markdown-it-katex from *@ryanxcharles*](https://www.npmjs.com/package/@ryanxcharles/markdown-it-katex)

As a consequence, this website also benefits from two very nice projects:
[highlight.js](https://highlightjs.org/) for syntax highlighting, and
[$\KaTeX$](https://katex.org/) for displaying mathematics equations.

## Frontend

In addition to [normalize.css](https://www.npmjs.com/package/normalize.css) to
“reset” the CSS defaults of various browsers, this website could not exist as it
is now without the awesome [Tufte
CSS](https://edwardtufte.github.io/tufte-css/) project. The sidenotes of this
website could not have existed without it.

## HTML Generation

While markdown-it is doing the heavy lifting of turning my Markdown contents
in HTML pages, [soupault](https://soupault.app) is the goldsmith which pieces
these pages together into a coherent whole.

I really enjoy using soupault for my website. In a nutshell, this tool enables
me to customize the pages of my website with an API very similar to what
Javascript offers, but instead of the computation happening on the client side
every time the page is loaded, it is done on my laptop once, just before I
push the new pages. Just an example: for my sidenote pages, I was able to reuse
the markdown-it-footnote with zero modification, and I just had to write a
simple Lua plugin to customize its output to my (humble) needs.

The [running log](/running.html) is also another good example of an ad hoc page
I can generate using a simple Lua script.
