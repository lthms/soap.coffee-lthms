---
published: 2024-05-23
tags: [neovim, releases]
abstract: |
    `hjkl` as motion keys always had one great drawback in my opinion: they
    required me to shift my left hand whenever I wanted to use them. When I
    switched to the [Bépo](https://bepo.fr) keyboard layout, I decided to right
    this wrong, and remapped `hjkl` to `tsrn` instead of `ctsr`.
---

# Introducing `bepo-tsrn.nvim`

It is not much, but I have recently [published on
GitHub](https://github.com/lthms/bepo-tsrn.nvim) what can be considered my very
first Neovim “plugin.”

`bepo-tsrn.nvim` is a zero-configuration, global plugin for Neovim which remaps
default Neovim bindings for the [Bépo](https://bepo.fr) keyboard layout. It
started as a fork of [`bepo.nvim`](https://github.com/cljoly/bepo.nvim) with
two significant changes:

- `hjkl` are remapped to `tsrn` instead of `ctsr`. `hjkl` as motion keys always
  had one great drawback in my opinion: they required me to shift my left hand
  whenever I wanted to use them. Well, no more!
- `bepo-tsrn.nvim` is a global plugin, unconditionally loaded at startup
  without the need to explicitely load it. As a consequence, it is a very
  convenient way to get Bépo enabled in Neovim system-wide. Bonus point if you
  are using Archlinux, since I have added it to the [Archlinux User
  Repository](https://aur.archlinux.org/packages/neovim-bepo-tsrn-git) (AUR).

`bepo-tsrn.nvim` is released under the terms of the Apache-2.0 license
(inherited from [`bepo.nvim`](https://github.com/cljoly/bepo.nvim)). Granted,
this plugin targets a very small niche of users, but maybe you will find it as
useful as I do!
