---
published: 2023-12-30
tags: ['spatial-shell', 'releases']
abstract: |
    After a first call for testers that could have been more effective if only
    the building instructions listed in the README were correct, I am quite
    happy to announce the 6th release for Spatial Shell that, I believe, is
    pretty usable for someone who _isn’t me_.
---

# Spatial Shell 6th Release Might Be the Charm

After a first [call for testers](/posts/CFTSpatialShell.html) that [could have
been more effective if only the building instructions listed in the README were
correct](https://github.com/lthms/spatial-shell/issues/2#issuecomment-1527193430),
I am quite happy to announce the 6th release for Spatial Shell that, I believe,
is pretty usable for someone who _isn’t me_.

## What’s Spatial Shell Already?

In a nutshell, Spatial Shell implements a _spatial model_ inspired by [Material
Shell](https://material-shell.com) for i3 and sway. Windows are organized in a
grid whose rows are your workspace, and you can navigate this grid (by focusing
neighbors windows), move the focused window around, decide how many window you
want to see at most in every workspace, etc.

When I first discovered Material Shell in August 2022, I was pretty excited,
but the fact that it is a GNOME extension prevented me from switching
completely (besides, it was pretty unstable on my laptop for reasons. So when I
discovered that Sway (my personal favorite window manager) could be controlled
by [a third-party program through a Unix
socket](https://man.archlinux.org/man/sway-ipc.7.en), I started experimenting.
[It didn’t take long before I had a working prototype that fit most of my
need](https://twitter.com/_lthms_/status/1561034295501897730), but it took a
significant amount of time to turn this prototype into something really usable
by anyone who isn’t me.

Here is a clunky showcase of what Spatial Shell can do[^aside].

@[video](https://spatial-shell.app/demo.mp4)

[^aside]: Yes, _Scott Pilgrim Takes Off_ is an awesome show that you definitely
    need to watch.

For the interested viewers, I am using a forked version of sway called
[SwayFX](https://github.com/WillPower3309/swayfx) to get these rounded corners
and the dim effects on unfocused windows. The status bar is Waybar with [a
config you can try yourself if you are
interested](https://github.com/lthms/spatial-shell/tree/main/contrib/waybar)!
There is also [a minimal `i3blocks`
config](https://github.com/lthms/spatial-shell/tree/main/contrib/i3blocks)
available if you cannot use Waybar[^i3].

To be clear, the UI part of Spatial Shell remains lacking to this day. My
Waybar configuration works, but is pretty verbose and statically limited. For
instance, it will only display the 8th first windows of a workspace. This is
because Waybar does not allow one widget to generate multiple blocks. The same
goes for the `i3blocks` configuration example. Also, they assume the
availability of a font with icons[^nerd-font].

[^nerd-font]: On that matter, I love the [Nerd
    Fonts](https://www.nerdfonts.com/) project.

[^i3]: I fully intend to provide an example config as visually pleasing as the
    one for Waybar, but compatible with i3.

## Try It Yourself!

As of today, you can install Spatial Shell using the following methods:

- By fetching the official binary builds for Linux x86_64 from the [GitHub
  releases page](https://github.com/lthms/spatial-shell/releases)
- By installing the [AUR package for
  Archlinux](https://aur.archlinux.org/packages/spatial-shell)
- By building directly from source

The [`README`](https://github.com/lthms/spatial-shell#spatial-shell) should be
a good starting point. If it is lacking key pieces of information, do not
hesitate to open an issue. At this point, I am willing to deal with
documentation issue as bugs.

Besides its `README`, Spatial Shell is documented via manpages. For a list of
available manpages, you can refer to `man -k spatial`. Spatial Shell definitely
works with sway, and should work with i3 since the former is basically a
drop-in replacement for the latter.

## Conclusion

The journey from the initial idea up to this moment has definitely been an
interesting one. At this point, Spatial Shell provides every feature I need.
That being said, it does not mean there is nothing more to tell! I certainly
hope this project will catch the eyes of some of you, and soon be used on
computers I do not own by folks who are not me.

Contributions are obviously welcome! Typically, if you happen to piece together
a neat status bar configuration, I am _very_ interested.
