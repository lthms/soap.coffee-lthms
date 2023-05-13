---
published: 2020-02-15
tags: ['releases']
abstract: |
    Introducing a new macro, more friendly with themes gallery like Peach
    Melpa.
---

# Release of `colorless-themes-0.2`

[I have tagged and released a new version of
`colorless-themes`](https://git.sr.ht/~lthms/colorless-themes.el/refs/0.2).
The motivation behind modifying the version number is an important breaking
change regarding how the `colorless-themes-make`{.lisp} macro shall be used.

Before `0.2`, the macro was calling `deftheme`{.lisp} and
`provide-theme`{.lisp} itself. In practices, it meant the actual themes were
not using these two functions themselves. It was working great in isolation,
but it turns out many tools such as `use-package`{.lisp} or [Peach
Melpa](https://peach-melpa.org) (an auto-generated Emacs themes gallery) are
relying on the presence of these functions to decide whether a file provides a
theme or not. As of now, `nordless-theme` and `lavenderless-theme` have been
updated accordingly, and [they appear on Peach
Melpa](https://peach-melpa.org/themes/lavenderless-theme/variants/lavenderless).
Their loading can also be defered using the `:defer`{.lisp} keyword of the
`use-package`{.lisp} macro.

if you happen to be a user of `colorless-themes`, feel free to shoot an email!
I would love to hear about your experience using a mostly colorless theme.
