---
published: 2022-08-15
modified: 2023-05-09
series:
  parent: series/Retrospectives.html
  next: posts/September2022.html
tags: ['emacs', 'meta']
abstract: |
    In an attempt to start a regular blogging habbits, I am giving a try to the
    monthly “status updates” format. This month: some Emacs config hacking, and
    some changes on how this website is generated.
---

# What happened in August 2022?

Without further ado, let’s take a look at what was achieved
for the last thirty days or so.

## Emacs

I have started tweaking and improving my Emacs
[configuration](https://src.soap.coffee/dotfiles/emacs.d.git)
again[^minimalism].

[^minimalism]: After having used Emacs for seven years now, I am nowhere close
    to consider my configuration as a done project. I really envy developers
    who are using their editor with little to no customization.

### Theme Selection Menu

The change I am the most excited about is that I have *finally* reduced the
boilerplate in need to write to use a new theme. I am very indecisive when
it comes to theming. I like to have my choices, and I get tired of any
colorscheme pretty quickly. As a consequence, I introduced a customizable
variable to let me select a theme dynamically, and have this choice persist
across Emacs session.

I have a Hydra menu that allows me to select which theme I want to
use for the time being. It looks like this.

#[A Hydra menu for selecting a theme.](/img/select-theme.png)

But adding new entries to this menu was very cumbersome, and mostly
boilerplate that I know a good macro could abstract away. And I can
finally report that I was right all along. I have my macros now,
and they allow me to have the Hydra menu above generated with these
simple lines of code.

```lisp
(use-theme ancientless "a" :straight nil :load-path "~/.emacs.d/lisp")
(use-theme darkless "d" :straight nil :load-path "~/.emacs.d/lisp")
(use-theme brightless "b" :straight nil :load-path "~/.emacs.d/lisp")
(use-theme monotropic "m")
(use-theme monokai "M")
(use-theme nothing "n")
(use-theme eink "e")
(use-theme dracula "D")
(use-theme chocolate "c")
(use-themes-from tao-theme
                 '(("tl" . tao-yang)
                   ("td" . tao-yin)))
```


### Eldoc and Flycheck Popups

I have been experimenting with several combinations of packages to
have Eldoc and Flycheck using pop-up-like mechanisms to report
things to me, instead of the echo area.

The winning setup for now is the one that uses the [`quick-peek`
package](https://github.com/cpitclaudel/quick-peek). That is,
[`flycheck-inline`](https://github.com/flycheck/flycheck-inline) (customized to
use quick-peek, as suggested in their README), and
[`eldoc-overlay`](https://melpa.org/#/eldoc-overlay). This works well enough,
so the pop-ups of eldoc are maybe a bit too distracting.

#[`flycheck-inline` in action with an OCaml compilation error.](/img/flycheck-inline.png)

In my quest for pop-ups, I ran into several issues with the packages I tried
out. For instance, [`eldoc-box`](https://github.com/casouri/eldoc-box) was very
nice, but also very slow for some reason. It turns out there were an issue
about that slowness, wherein the culprit was identified. This allowed me to
[submit a pull request that got merged rather
quickly](https://github.com/casouri/eldoc-box/pull/48).

Similarly, after a packages update, I discovered
[`flycheck-ocaml`](https://github.com/flycheck/flycheck-ocaml) was no longer
working, and [submit a patch to fix the
issue](https://github.com/flycheck/flycheck-ocaml/pull/14).

## This Website
  I have not been investing a lot of time in this website for the past
  six years or so. This month, things change a bit on that side too.

### New Contents

First, I have published a (short) article on [higher-order
polymorphism in OCaml](/posts/RankNTypesInOCaml.html). The goal was for me to
log somewhere the solution for an odd problem I was confronted to at
`$WORK`{.bash}, but the resulting article was not doing a great job as
conveying this. In particular, two comments on Reddit motivated me to rework
it, and I am glad I did. I hope you enjoy the retake.

Once this was out of the way, I decided that generating this website was taking
way too much time for no good enough reason. The culprit was **`cleopatra`**, a
toolchain I had developed in 2020 to integrate the build process of this
website as additional contents that I thought might interest people. The sad
things were: **`cleopatra`** was adding a significant overhead, and I never take
the time to actually document them properly.

### Under the Hood

Overall, the cost of using **`cleopatra`** was not worth the burden, and so I
got ride of it. Fortunately, it was not very difficult, since the job of
**`cleopatra`** was to extracting the generation processes from org files; I
just add to implement a small `makefile` to make use of these files, without
having to rely on **`cleopatra`** anymore.

This was something I was pondering to do for a long time, and as
often in these circumstances, this gave me the extra motivation I
needed to tackle other ideas I had in mind for this website. This
is why now, rather than starting one Emacs process per Org file I
have to process, my build toolchain starts one Emacs server, and
later uses `emacsclient`.

Now, most of the build time is spent by [soupault](https://soupault.app). I guess
I will have to spend some time on the Lua plugins I have developed for it at
some point.

## A New Mailing List

Finally, I have created [a public
mailing](https://lists.sr.ht/~lthms/public-inbox) list that is available if you
want to start a discussion on one of my article. Don’t hesitate to use it, or
to register to it!
