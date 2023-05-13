---
published: 2022-09-18
modified: 2023-05-09
series:
  parent: series/Retrospectives.html
  prev: posts/August2022.html
  next: posts/November2022.html
tags: ['spatial-shell', 'meta']
abstract: |
    In a nutshell, my latest hobby project (Spatial Sway) works well enough
    so that I can use it daily, and I have done some unsuccessful experiments
    for this website.
---

# What happened in September 2022?

It is September 18 today, and it has already been a month since I
decided to start these retrospectives. This means it is time to take a
step back and reflect of what happened these past few thirty days or
so[^syntax].

[^syntax]: There is the shocking news that I have started to use syntax
    highlighting again. But let’s not dwelve too much into it just yet.

## Spatial Sway

A few days after publishing my August Retrospective, I have learnt
the existence of [Material Shell](https://material-shell.com), an extension for
GNOME 3 that provides a very interesting user experience.

I tried it for a few hours, but the thing kept crashing (it’s
probably on me, I did not even remember I had Gnome installed on my
machine, and I would not be surprised the culprit was my dusty setup
rather than Material Shell itself). The experience remained very
promising, though. Their “spatial model” especially felt like a very
good fit for me. Basically, the main idea is that you have a grid of
windows, with your workspaces acting as the rows. You can navigate
horizontally (from one workspace to another), or horizontally, and
you choose how many windows you want to see at once on your screen.

And so for a few hours, I was a bit frustrated by the situation…
until I learnt about how one can actually manage and extend Sway
(the Wayland compositor I use for several years now) thanks to its IPC
protocol.  I spend like three days experimenting, first in Rust, then in
OCaml[^ocaml], and by the end of the week, I had a first working prototype I
called [Spatial Sway](https://github.com/lthms/spatial-shell). It works pretty
well, enough at least that I am using it daily for several weeks now. It feels
clunky at time, but it works well, and I have been able to write a
[Waybar](https://github.com/Alexays/Waybar) configuration heavily inspired on
Material Shell UI.

[^ocaml]: This was actually an interesting thought process. I am using OCaml at
    `$WORK`{.bash} for about more than a year now.

    I have curated a setup that works pretty well, and I am familiar with the
    development tools. On the contrary, I had not written a line of Rust for at
    least a year, my Emacs configuration for this language was broken, and I
    had lost all my fluancy in this language. Still, I was not expecting to
    pick OCaml when I started this project.

Overall, I am pretty satisfied with this turnout. Writing a hobbyist
software project is always nice, but the one you can integrate in
your daily workflow are the best one. The last time I did that was
[**keyrd**](https://sr.ht/~lthms/keyrd), my little keystrokes counting
daemon[^keyrcount].

[^keyrcount]: 19,970,965 since I started using it at the time of writing this
    article

Anyway, lots remain to be said about Spatial Sway, but I might save
it for a bit later. I still have some key features to implement
(notably, moving a window to another workspaces), then I will
probably try to advertise it a bit. I am under the impression this
project could be of interest for other, and I would love to see it
used by folks willing to give a Material Shell-like experience a
try, without having to deal with Gnome Shell. By the way,
considering Sway is a drop-in replacement for i3, and that it
implements the exact same IPC protocol, there is no reason why
Spatial Sway is actually Sway specific, and I will rename it Spatial
Shell at some point.

#[Mandatory screenshot of Spatial Sway.](/img/spatial-sway-preview.png)

## This Website

On a side note, I have started to refine the layout of this website
a bit. Similarly, I have written a new, curated home page where I
want to highlight the most recent things I have published on the
Internet.

I have been experimenting with
[Alectryon](https://github.com/cpitclaudel/alectryon/) as a way to replace
`coqdoc`, to improve the readability of my Coq-related articles. Unfortunately,
it looks like this tool is missing [a key feature I
need](https://github.com/cpitclaudel/alectryon/issues/86). I might try to get
my hand dirty and implement it my self, if I find the time and the motivation
in the following weeks.

Finally, reading about how [Xe Iaso’s talk about how she generates her
blog](https://xeiaso.net/talks/how-my-website-works) was very inspiring too me.
I can only suggest you to have a look.

Though not to the same extend, Ialso think I have spent way too much effort in
my website. Most of my Coq-related articles are actual Coq program, expect the
articles about `coqffi` which are actual literate programs. Hell, this website
itself used to be a literate program of sort, until I stopped using my
homegrown literate programming toolchain **`cleopatra`** last month. At some
point, I have even spent a bit of time to ensure most of the pages of this
website were granted a 100/100 on websites like PageSpeed Insight[^goodnews]. I
had almost forgot.

[^goodnews]: Good news, I’ve just checked, and it still is!

A lot remains to be done, but watching this talk made me reflect on
the job done. And opened my eyes to new perspective, too. We will
see what translates into reality.
