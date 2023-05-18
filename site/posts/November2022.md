---
published: 2022-11-19
modified: 2023-05-09
tags: ['spatial-shell', 'nanowrimo', 'coqffi']
series:
  parent: series/Retrospectives.html
  prev: posts/September2022.html
  next: posts/May2023.html
abstract: |
    Spatial Sway has basically reached the MVP stage, I failed to fully commit
    to this year’s NaNoWriMo, and someone has worked on adding some support for
    `coqffi` to `dune`.
---

# What happened in October and November 2022?

It is November 19 today, and I’m one month and 4 days late for the October
Retrospective! Truth is, `$WORK`{.bash} has been intense lately, to a point
where I have not made much progress on my side projects. Anyway.

I have implemented the last feature I was really missing in my daily
use of Spatial Sway: moving windows to adjacent workspaces. As a
result, I think I can say that Spatial Sway has really reached the
“Minimum Viable Product” stage, with a convenient UX, and a nice
enough UI. It is still lacking when it comes to configurability,
though. It is the next item of my TODO list, but I have no idea when I
will implement the support for a configuration file.

Another highlight of the past two months was the
[NaNoWriMo](https://nanowrimo.org). I took the last week of October and the
first week of November off to plan and start writing a fiction project for it.
Writing again was really nice, and I even gave writing fiction in English a
shot. That made me uncover a bug in the English support of
[ogam](https://crates.io/crates/ogam), my markup language for fiction writers,
which led me to publish a fix on Crates.io. However, as soon as I came back to
`$WORK`{.bash}, my writing spree ended. That’s okay, though. It gave me plenty
of ideas for future sessions. Thanks, NaNoWriMo! Sorry to quit so soon, and see
you next year, maybe.

Finally, a nice surprise of the past month is that [someone has started working
on adding proper support for `coqffi` to
`dune`](https://github.com/ocaml/dune/pull/6489), the build system for OCaml
and Coq! I’m thrilled by this. Thanks,
[**@Alizter**](https://github.com/Alizter)!

This wraps up this retrospective. I hope I will have more interesting,
concrete news to share next month.
